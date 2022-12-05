import Lean

open Lean

-- Disjoint set implementing congruence closure with proofs.
def DisjointSet := HashMap FVarId (FVarId × Expr)

namespace DisjointSet

def empty : DisjointSet := HashMap.empty

def fvars (ds : DisjointSet) : List FVarId := ds.toList.map (·.1)

def contains (ds : DisjointSet) (fv : FVarId) := HashMap.contains ds fv

def insert (ds : DisjointSet) (fv : FVarId) : MetaM DisjointSet := do
  if !ds.contains fv then
    let p ← Meta.mkAppM `Eq.refl #[.fvar fv]
    return HashMap.insert ds fv (fv, p)
  return ds

partial def find! (ds : DisjointSet) (fv : FVarId) : MetaM (FVarId × Expr) := do
  let mut fv₂ := fv
  let mut (fv₁, p₂₁) := HashMap.find! ds fv₂
  if fv₁ != fv₂ then
    let (fv₀, p₁₀) ← ds.find! fv₁
    let mv := (← Meta.mkFreshExprMVar (← Meta.mkAppM ``Eq #[.fvar fv₂, .fvar fv₀])).mvarId!
    let r ← mv.rewrite (← mv.getType) p₂₁ false (.pos [1])
    let mut mv' ← mv.replaceTargetEq r.eNew r.eqProof
    let r ← mv'.rewrite (← mv'.getType) p₁₀ false (.pos [1])
    mv' ← mv'.replaceTargetEq r.eNew r.eqProof
    mv'.refl
    fv₁ := fv₀
    p₂₁ := .mvar mv
  return (fv₁, p₂₁)

def find (ds : DisjointSet) (fv : FVarId) : MetaM (DisjointSet × FVarId × Expr) := do
  let mut ds := ds
  if !ds.contains fv then
    ds ← ds.insert fv
  return (ds, ← ds.find! fv)

def union! (ds : DisjointSet) (fv₂ : FVarId) (fv₁ : FVarId) (p₂₁ : Expr) : MetaM DisjointSet := do
  let (fv₁', p₁₁) ← ds.find! fv₁
  let (fv₂', p₂₂) ← ds.find! fv₂
  if (fv₁' != fv₂') then
    let mv := (← Meta.mkFreshExprMVar (← Meta.mkAppM ``Eq #[.fvar fv₂', .fvar fv₁'])).mvarId!
    let r ← mv.rewrite (← mv.getType) p₁₁ true (.pos [1])
    let mut mv' ← mv.replaceTargetEq r.eNew r.eqProof
    let r ← mv'.rewrite (← mv'.getType) p₂₂ true (.pos [1])
    mv' ← mv'.replaceTargetEq r.eNew r.eqProof
    mv'.assign p₂₁
    return HashMap.insert ds fv₂' (fv₁', .mvar mv)
  return ds

def union (ds : DisjointSet) (fv₂ : FVarId) (fv₁ : FVarId) (p₂₁ : Expr) : MetaM DisjointSet := do
  let mut ds := ds
  if !ds.contains fv₁ then
    ds ← ds.insert fv₁
  if !ds.contains fv₂ then
    ds ← ds.insert fv₂
  ds.union! fv₂ fv₁ p₂₁

private def newHypName (mv : MVarId) : MetaM Name := do
  return Lean.LocalContext.getUnusedName (← mv.getDecl).lctx `hds

def updateCtx (ds : DisjointSet) (mv : MVarId) : MetaM MVarId := mv.withContext do
  let mut mv := mv
  let mut cache := HashSet.empty
  for fv in (← mv.getDecl).lctx.getFVarIds do
    cache := cache.insert (← fv.getType)
  let fvs := ds.fvars
  for fv₁ in fvs do
    for fv₂ in fvs do
      if (← fv₁.getType) != (← fv₂.getType) then
        continue
      let eq ← Meta.mkAppM ``Eq #[.fvar fv₂, .fvar fv₁]
      if !cache.contains eq then
        let (fv₁', p₁₁) ← ds.find! fv₁
        let (fv₂', p₂₂) ← ds.find! fv₂
        if fv₁' == fv₂' then
          let mv' := (← Meta.mkFreshExprMVar eq).mvarId!
          let r ← mv'.rewrite (← mv'.getType) p₁₁ false (.pos [1])
          let mut mvt ← mv'.replaceTargetEq r.eNew r.eqProof
          let r ← mvt.rewrite (← mvt.getType) p₂₂ false (.pos [1])
          mvt ← mvt.replaceTargetEq r.eNew r.eqProof
          mvt.refl
          (_, mv) ← (← mv.assert (← newHypName mv) eq (.mvar mv')).intro1P
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

end DisjointSet
