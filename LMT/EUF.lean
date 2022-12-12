import LMT.Base
import Lean

open Lean in
def Lean.DisjointSet := HashMap FVarId (FVarId × Expr)

namespace Lean.Meta

open Lean

structure EUF.State where
  -- Disjoint set implementing congruence closure with proofs.
  ds : DisjointSet := HashMap.empty

abbrev EUFM := StateT EUF.State BaseM

namespace EUF

def fvars : EUFM (List FVarId) := return (← get).ds.toList.map (·.1)

def contains (fv : FVarId) : EUFM Bool := return HashMap.contains (← get).ds fv

def insert (fv : FVarId) : EUFM Unit := do
  let mut ⟨ds⟩ ← get
  if !ds.contains fv then
    let p ← Meta.mkAppM `Eq.refl #[.fvar fv]
    set ({ds := HashMap.insert ds fv (fv, p)} : State)

partial def find! (fv : FVarId) : EUFM (FVarId × Expr) := do
  let mut fv₂ := fv
  let mut (fv₁, p₂₁) := HashMap.find! (← get).ds fv₂
  if fv₁ != fv₂ then
    let (fv₀, p₁₀) ← find! fv₁
    let mv := (← Meta.mkFreshExprMVar (← Meta.mkAppM ``Eq #[.fvar fv₂, .fvar fv₀])).mvarId!
    let r ← mv.rewrite (← mv.getType) p₂₁ false (.pos [1])
    let mut mv' ← mv.replaceTargetEq r.eNew r.eqProof
    let r ← mv'.rewrite (← mv'.getType) p₁₀ false (.pos [1])
    mv' ← mv'.replaceTargetEq r.eNew r.eqProof
    mv'.refl
    fv₁ := fv₀
    p₂₁ := .mvar mv
  return (fv₁, p₂₁)

def find (fv : FVarId) : EUFM (FVarId × Expr) := do
  if !(← contains fv) then
    insert fv
  find! fv

def union! (fv₂ : FVarId) (fv₁ : FVarId) (p₂₁ : Expr) : EUFM Unit := do
  let (fv₁', p₁₁) ← find! fv₁
  let (fv₂', p₂₂) ← find! fv₂
  if (fv₁' != fv₂') then
    let mv := (← Meta.mkFreshExprMVar (← Meta.mkAppM ``Eq #[.fvar fv₂', .fvar fv₁'])).mvarId!
    let r ← mv.rewrite (← mv.getType) p₁₁ true (.pos [1])
    let mut mv' ← mv.replaceTargetEq r.eNew r.eqProof
    let r ← mv'.rewrite (← mv'.getType) p₂₂ true (.pos [1])
    mv' ← mv'.replaceTargetEq r.eNew r.eqProof
    mv'.assign p₂₁
    set ({ds := HashMap.insert (← get).ds fv₂' (fv₁', .mvar mv)} : State)

def union (fv₂ : FVarId) (fv₁ : FVarId) (p₂₁ : Expr) : EUFM Unit := do
  if !(← contains fv₁) then
    insert fv₁
  if !(← contains fv₂) then
    insert fv₂
  union! fv₂ fv₁ p₂₁

def updateCtx (mv : MVarId) : EUFM MVarId := mv.withContext do
  let mut mv := mv
  let mut cache := HashSet.empty
  for fv in (← mv.getDecl).lctx.getFVarIds do
    cache := cache.insert (← fv.getType)
  let fvs ← fvars
  for fv₁ in fvs do
    for fv₂ in fvs do
      if (← fv₁.getType) != (← fv₂.getType) then
        continue
      let eq ← Meta.mkAppM ``Eq #[.fvar fv₂, .fvar fv₁]
      if !cache.contains eq then
        let (fv₁', p₁₁) ← find! fv₁
        let (fv₂', p₂₂) ← find! fv₂
        if fv₁' == fv₂' then
          let mv' := (← Meta.mkFreshExprMVar eq).mvarId!
          let r ← mv'.rewrite (← mv'.getType) p₁₁ false (.pos [1])
          let mut mvt ← mv'.replaceTargetEq r.eNew r.eqProof
          let r ← mvt.rewrite (← mvt.getType) p₂₂ false (.pos [1])
          mvt ← mvt.replaceTargetEq r.eNew r.eqProof
          mvt.refl
          (_, mv) ← (← mv.assert (← Base.newHypName) eq (.mvar mv')).intro1P
  return mv

private def toMessageData (ds : DisjointSet) : MessageData :=
  let m := ds.fold (fun s fv₂ _ => Id.run do
    let mut s := s ++ m!"{Expr.fvar fv₂}"
    let mut fv₂ := fv₂
    let mut (fv₁, _) := HashMap.find! ds fv₂
    while fv₁ != fv₂ do
      fv₂ := fv₁
      (fv₁, _) := HashMap.find! ds fv₂
      s := s ++ m!" → {Expr.fvar fv₂}"
    return s ++ m!", ") m!""
  MessageData.bracket "{" m "}"

instance : ToMessageData DisjointSet := ⟨toMessageData⟩

def congrClosure (mv : MVarId) : EUFM MVarId := mv.withContext do
  let mut mv := mv
  let mut posEqns := []
  for fv in (← mv.getDecl).lctx.getFVarIds do
    if let some (_, lhs, rhs) := (← fv.getType).eq? then
      if rhs.isFVar then
        union lhs.fvarId! rhs.fvarId! (.fvar fv)
      else
        posEqns := fv :: posEqns
  congrs posEqns
  mv ← updateCtx mv
  return mv
where
  congr (fv₂ : FVarId) (fv₁ : FVarId) : EUFM Unit := do
    let some (_, .fvar x₁, f₁) := (← fv₁.getType).eq? | throwError "something went wrong"
    let some (_, .fvar x₂, f₂) := (← fv₂.getType).eq? | throwError "something went wrong"
    let (x₁', _) ← find x₁
    let (x₂', _) ← find x₂
    if x₁' == x₂' || f₁.getAppFn != f₂.getAppFn then
      return
    let mv := (← Meta.mkFreshExprMVar (← Meta.mkAppM ``Eq #[.fvar x₂, .fvar x₁])).mvarId!
    let r ← mv.rewrite (← mv.getType) (.fvar fv₁) false (.pos [1])
    let mut mv' ← mv.replaceTargetEq r.eNew r.eqProof
    let r ← mv'.rewrite (← mv'.getType) (.fvar fv₂) false (.pos [1])
    mv' ← mv'.replaceTargetEq r.eNew r.eqProof
    let fas₁ := f₁.getAppArgs
    let fas₂ := f₂.getAppArgs
    for (fa₁, fa₂) in fas₁.zip fas₂ do
      if fa₁ == fa₂ then
        continue
      let (.fvar fa₁, .fvar fa₂) := (fa₁, fa₂) | throwError "something went wrong"
      let (fa₁', p₁₁) ← find fa₁
      let (fa₂', p₂₂) ← find fa₂
      if fa₁' != fa₂' then
        return
      let r ← mv'.rewrite (← mv'.getType) p₁₁ false (.pos [1])
      mv' ← mv'.replaceTargetEq r.eNew r.eqProof
      let r ← mv'.rewrite (← mv'.getType) p₂₂ false (.pos [1])
      mv' ← mv'.replaceTargetEq r.eNew r.eqProof
    mv'.refl
    union! x₂ x₁ (.mvar mv)
  congrs (fvs : List FVarId) : EUFM Unit := do
    for fv₁ in fvs do
      for fv₂ in fvs do
        congr fv₁ fv₂

end EUF

def congrClosure (mv : MVarId) : MetaM MVarId := EUF.congrClosure mv
  |>.run' { }
  |>.run' { mv := mv }

private def newHypName (mv : MVarId) : MetaM Name := do
  return Lean.LocalContext.getUnusedName (← mv.getDecl).lctx `h

syntax (name := euf) "euf" : tactic

open Elab Tactic in
@[tactic euf] def evalEuf : Tactic := fun _ => do
  let mut mv ← Tactic.getMainGoal
  while (← mv.getType).isArrow do
    (_, mv) ← mv.intro (← newHypName mv)
  mv ← congrClosure mv
  Tactic.replaceMainGoal [mv]
  mv.contradiction

end Lean.Meta
