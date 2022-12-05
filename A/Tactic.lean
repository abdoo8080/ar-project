import A.A
import A.EUF
import Lean

open Lean Elab Tactic

namespace Lean.Expr

@[inline] def read? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity `A.read 5 then
    some (e.getArg! 3, e.getArg! 4)
  else
    none

@[inline] def write? (e : Expr) : Option (Expr × Expr × Expr) :=
  if e.isAppOfArity `A.write 6 then
    some (e.getArg! 3, e.getArg! 4, e.getArg! 5)
  else
    none

@[inline] def eqRead? (e : Expr) : Option (Expr × Expr × Expr) :=
  match e.eq? with
  | some (_, v, e) => match e.read? with
    | some (a, i) => some (v, a, i)
    | _ => none
  | _ => none

@[inline] def eqWrite? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
  match e.eq? with
  | some (_, a, e) => match e.write? with
    | some (b, i, v) => some (a, b, i, v)
    | _ => none
  | _ => none

end Lean.Expr

namespace Solver

structure State where
  lits : List Expr := []

abbrev SolverM := StateT State MetaM

def newHypName (mv : MVarId) : MetaM Name := do
  return Lean.LocalContext.getUnusedName (← mv.getDecl).lctx `h

def newVarName (mv : MVarId) : MetaM Name := do
  return Lean.LocalContext.getUnusedName (← mv.getDecl).lctx `x

def newMVarName (mv : MVarId) : MetaM Name := do
  return Lean.LocalContext.getUnusedName (← mv.getDecl).lctx `m

def applyRfl (mv : MVarId) (fv : FVarId) : MetaM MVarId := mv.withContext do
  if (← fv.getType).isAppOf ``A then
      let p ← Meta.mkAppM ``Eq.refl #[.fvar fv]
      let t ← Meta.inferType p
      return (← (← mv.assert (← newHypName mv) t p).intro1P).snd
  return mv

def applyRfls (mv : MVarId) : MetaM MVarId := do
  let mut mv := mv
  for fv in (← mv.getDecl).lctx.getFVarIds do
    mv ← applyRfl mv fv
  return mv

def applySymm (mv : MVarId) (fv : FVarId) : MetaM MVarId := mv.withContext do
  if let some (_, lhs, rhs) := (← fv.getType).eq? then
    if lhs != rhs && lhs.isFVar && rhs.isFVar then
      let t ← Meta.mkAppM ``Eq #[rhs, lhs]
      let p ← Meta.mkAppM ``Eq.symm #[.fvar fv]
      return (← (← mv.assert (← newHypName mv) t p).intro1P).snd
  return mv

def applySymms (mv : MVarId) : MetaM MVarId := do
  let mut mv := mv
  for fv in (← mv.getDecl).lctx.getFVarIds do
    mv ← applySymm mv fv
  return mv

def applyRIntro1s (mv : MVarId) : MetaM MVarId := do
  let mut mv := mv
  for fv in (← mv.getDecl).lctx.getFVarIds do
    mv ← applyRIntro1 mv fv
  return mv
where
  applyRIntro1 (mv : MVarId) (fv : FVarId) : MetaM MVarId := mv.withContext do
    match ← fv.getType with
    | (.app (.app (.app (.const ``Eq _) _) _)
            (.app (.app (.app (.app (.app (.app (.const ``A.write _) _) _) _) _) _) _)) =>
      let p ← Meta.mkAppM ``A.r_intro1 #[.fvar fv]
      let t ← Meta.inferType p
      let (_, mv) ← (← mv.assert (← newHypName mv) t p).intro1P
      return mv
    | _ => return mv

abbrev CacheList := List (Expr × Expr × Expr × Expr)

def applyRIntro2 (mv : MVarId) (fv1 : FVarId) (fv2 : FVarId) (fv3 : FVarId) : StateT CacheList MetaM (List MVarId) := mv.withContext do
  match (← fv1.getType).eq?, (← fv2.getType).eqWrite?, (← fv3.getType).eqRead? with
  | some (_, d, e), some (a, b, i, v), some (x, c, j) =>
    if (i != j) && (d == a || d == b) && e == c then
      if !(← get).contains (a, b, i, j) then
        modify ((a, b, i, j) :: (b, a, i, j) :: ·)
        let eq1 ← Meta.mkAppM ``Eq #[a, c]
        let eq2 ← Meta.mkAppM ``Eq #[b, c]
        let mut omv := (← Meta.mkFreshExprMVar (← Meta.mkAppM ``Or #[eq1, eq2])).mvarId!
        let p ← Meta.mkAppM ``A.r_intro2 #[.mvar omv, .fvar fv2, .fvar fv3]
        let t ← Meta.inferType p
        let (fv, mv) ← (← mv.assert (← newHypName mv) t p).intro1P
        omv := (← omv.apply (mkConst (if d == a then ``Or.inl else ``Or.inr)))[0]!
        omv.assign (.fvar fv1)
        let #[sg1, sg2] ← mv.cases fv #[⟨false, [← newHypName mv]⟩, ⟨false, [← newHypName mv]⟩] |
          throwError "RIntro2 case split failed."
        let mv1 := sg1.mvarId
        let mv2 := sg2.mvarId
        let fv2 := sg2.fields[0]!.fvarId!
        let (_, _, fv2, mv2) ← replaceLHS mv2 fv2
        let (_, _, _, mv2) ← replaceRHS mv2 fv2
        return [mv1, mv2]
    return []
  | _, _, _ => return []
where
  findFVOrCreate (mv : MVarId) (e : Expr) : MetaM (FVarId × FVarId × MVarId) := mv.withContext do
    for fv in (← mv.getDecl).lctx.getFVarIds do
      if let some (_, x, e') := (← fv.getType).eq? then
        if e' == e then
          return (x.fvarId!, fv, mv)
    let (x, mv) ← (← mv.assertExt (← newVarName mv) (← Meta.inferType e) e).intro1P
    let (fv, mv) ← mv.intro1P
    return (x, fv, mv)
  replaceLHS (mv : MVarId) (fv : FVarId) : MetaM (FVarId × FVarId × FVarId × MVarId) := mv.withContext do
    let some (_, lhs, rhs) := (← fv.getType).eq? | throwError "something went wrong..."
    let (x, xfv, mv) ← findFVOrCreate mv lhs
    mv.withContext do
    let xt ← Meta.mkAppM ``Eq #[.fvar x, rhs]
    let xmv := (← Meta.mkFreshExprMVar (← Meta.mkAppM ``Eq #[← fv.getType, xt])).mvarId!
    let ⟨fv, mv, _⟩ ← mv.replaceLocalDecl fv xt (.mvar xmv)
    let r ← xmv.rewrite (← xmv.getType) (.fvar xfv)
    let xmv ← xmv.replaceTargetEq r.eNew r.eqProof
    xmv.refl
    return (x, xfv, fv, mv)
  replaceRHS (mv : MVarId) (fv : FVarId) : MetaM (FVarId × FVarId × FVarId × MVarId) := mv.withContext do
    let some (_, lhs, rhs) := (← fv.getType).eq? | throwError "something went wrong..."
    let (y, yfv, mv) ← findFVOrCreate mv rhs
    mv.withContext do
    let yt ← Meta.mkAppM ``Eq #[lhs, .fvar y]
    let ymv := (← Meta.mkFreshExprMVar (← Meta.mkAppM ``Eq #[← fv.getType, yt])).mvarId!
    let ⟨fv, mv, _⟩ ← mv.replaceLocalDecl fv yt (.mvar ymv)
    let r ← ymv.rewrite (← ymv.getType) (.fvar yfv)
    let ymv ← ymv.replaceTargetEq r.eNew r.eqProof
    ymv.refl
    return (y, yfv, fv, mv)

def product (xs : List α) (ys : List β) : List (α × β) := Id.run do
  let mut zs := []
  for x in xs do
    for y in ys do
      zs := (x, y) :: zs
  return zs

partial def applyRIntro2s (cache : CacheList) (mv : MVarId) : MetaM (List MVarId) := do
  let fvs := (← mv.getDecl).lctx.getFVarIds.toList
  let mut mvs := []
  let mut cache := cache
  for (fv1, fv2, fv3) in product fvs (product fvs fvs) do
    (mvs, cache) ← StateT.run (applyRIntro2 mv fv1 fv2 fv3) cache
    if !mvs.isEmpty then
      break
  if mvs.isEmpty then
    return [mv]
  else
    return (← applyRIntro2s cache mvs[0]!) ++ (← applyRIntro2s cache mvs[1]!)

def applyExt (mv : MVarId) (fv : FVarId) : MetaM MVarId := mv.withContext do
  match ← fv.getType with
  | (.app (.app (.app (.const ``Ne _) _) _) _) =>
    let p ← Meta.mkAppM ``A.ext #[.fvar fv]
    let t ← Meta.inferType p
    let mut (fv, mv) ← (← mv.assert (← newHypName mv) t p).intro1P
    (_, fv, mv) ← introExists mv fv
    (_, _, fv, mv) ← replaceLHS mv fv
    (_, _, fv, mv) ← replaceRHS mv fv
    return mv
  | _ => return mv
where
  introExists (mv : MVarId) (fv : FVarId) : MetaM (FVarId × FVarId × MVarId) := do
    let #[sg] ← mv.cases fv #[⟨false, [← newVarName mv, ← newHypName mv]⟩] | throwError "Exists intro failed."
    return (sg.fields[0]!.fvarId!, sg.fields[1]!.fvarId!, sg.mvarId)
  replaceLHS (mv : MVarId) (fv : FVarId) : MetaM (FVarId × FVarId × FVarId × MVarId) := do
    let lhs ← getLHS fv mv
    let rhs ← getRHS fv mv
    let (x, mv) ← (← mv.assertExt (← newVarName mv) (← Meta.inferType lhs) lhs).intro1P
    let (xfv, mv) ← mv.intro1P
    mv.withContext do
    let xt ← Meta.mkAppM ``Ne #[.fvar x, rhs]
    let xmv := (← Meta.mkFreshExprMVar (← Meta.mkAppM ``Eq #[← fv.getType, xt])).mvarId!
    let ⟨fv, mv, _⟩ ← mv.replaceLocalDecl fv xt (.mvar xmv)
    let r ← xmv.rewrite (← xmv.getType) (.fvar xfv)
    let xmv ← xmv.replaceTargetEq r.eNew r.eqProof
    xmv.refl
    return (x, xfv, fv, mv)
  replaceRHS (mv : MVarId) (fv : FVarId) : MetaM (FVarId × FVarId × FVarId × MVarId) := do
    let lhs ← getLHS fv mv
    let rhs ← getRHS fv mv
    let (y, mv) ← (← mv.assertExt (← newVarName mv) (← Meta.inferType rhs) rhs).intro1P
    let (yfv, mv) ← mv.intro1P
    mv.withContext do
    let yt ← Meta.mkAppM ``Ne #[lhs, .fvar y]
    let ymv := (← Meta.mkFreshExprMVar (← Meta.mkAppM ``Eq #[← fv.getType, yt])).mvarId!
    let ⟨fv, mv, _⟩ ← mv.replaceLocalDecl fv yt (.mvar ymv)
    let r ← ymv.rewrite (← ymv.getType) (.fvar yfv)
    let ymv ← ymv.replaceTargetEq r.eNew r.eqProof
    ymv.refl
    return (y, yfv, fv, mv)
  getLHS (fv : FVarId) (mv : MVarId) : MetaM Expr := mv.withContext do
    let p ← fv.getType
    let (.app (.app (.app (.const ``Ne _) _) lhs) _) := p | throwError "Something went wrong..."
    return lhs
  getRHS (fv : FVarId) (mv : MVarId) : MetaM Expr := mv.withContext do
    let p ← fv.getType
    let (.app (.app (.app (.const ``Ne _) _) _) rhs) := p | throwError "Something went wrong..."
    return rhs

def applyExts (mv : MVarId) : MetaM MVarId := do
  let mut mv := mv
  for fv in (← mv.getDecl).lctx.getFVarIds do
    mv ← applyExt mv fv
  return mv

syntax (name := arr) "arr" : tactic

@[tactic arr] def evalArr : Tactic := fun _ => do
  let mut mv ← Tactic.getMainGoal
  while (← mv.getType).isArrow do
    (_, mv) ← mv.intro (← newHypName mv)
  mv ← EUF.congrClosure mv
  mv ← applyExts mv
  mv ← applyRIntro1s mv
  Tactic.replaceMainGoal [mv]
  let mvs ← applyRIntro2s [] mv
  let mut mvs' := []
  for mv' in mvs do
    let mv' ← EUF.congrClosure mv'
    try
      mv'.contradiction
    catch _ =>
      mvs' := mv' :: mvs'
  Tactic.replaceMainGoal mvs'

end Solver
