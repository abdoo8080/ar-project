import Lean
import A.DisjointSet

namespace EUF

open Lean Elab Tactic

private def newHypName (mv : MVarId) : MetaM Name := do
  return Lean.LocalContext.getUnusedName (← mv.getDecl).lctx `heuf

def congrClosure (mv : MVarId) : MetaM MVarId := mv.withContext do
  let mut mv := mv
  let mut posEqns := []
  let mut ds := DisjointSet.empty
  for fv in (← mv.getDecl).lctx.getFVarIds do
    if let some (_, lhs, rhs) := (← fv.getType).eq? then
      if rhs.isFVar then
        ds ← ds.union lhs.fvarId! rhs.fvarId! (.fvar fv)
      else
        posEqns := fv :: posEqns
  ds ← congrs ds posEqns
  mv ← ds.updateCtx mv
  return mv
where
  congr (ds : DisjointSet) (fv₂ : FVarId) (fv₁ : FVarId) : MetaM DisjointSet := do
    let mut ds := ds
    let some (_, .fvar x₁, f₁) := (← fv₁.getType).eq? | throwError "something went wrong"
    let some (_, .fvar x₂, f₂) := (← fv₂.getType).eq? | throwError "something went wrong"
    ds ← ds.insert x₁
    ds ← ds.insert x₂
    let (x₁', _) ← ds.find! x₁
    let (x₂', _) ← ds.find! x₂
    if x₁' == x₂' || f₁.getAppFn != f₂.getAppFn then
      return ds
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
      ds ← ds.insert fa₁
      ds ← ds.insert fa₂
      let (fa₁', p₁₁) ← ds.find! fa₁
      let (fa₂', p₂₂) ← ds.find! fa₂
      if fa₁' != fa₂' then
        return ds
      let r ← mv'.rewrite (← mv'.getType) p₁₁ false (.pos [1])
      mv' ← mv'.replaceTargetEq r.eNew r.eqProof
      let r ← mv'.rewrite (← mv'.getType) p₂₂ false (.pos [1])
      mv' ← mv'.replaceTargetEq r.eNew r.eqProof
    mv'.refl
    ds.union! x₂ x₁ (.mvar mv)
  congrs (ds : DisjointSet) (fvs : List FVarId) : MetaM DisjointSet := do
    let mut ds := ds
    for fv₁ in fvs do
      for fv₂ in fvs do
        ds ← congr ds fv₁ fv₂
    return ds

syntax (name := euf) "euf" : tactic

@[tactic euf] def evalEuf : Tactic := fun _ => do
  let mut mv ← Tactic.getMainGoal
  while (← mv.getType).isArrow do
    (_, mv) ← mv.intro (← newHypName mv)
  mv ← congrClosure mv
  Tactic.replaceMainGoal [mv]
  mv.contradiction

end EUF

