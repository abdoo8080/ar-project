import LMT.A
import LMT.Base
import LMT.EUF
import Lean

namespace Lean.Expr

@[inline] def eqFV? (e : Expr) : Option (Expr × Expr) :=
  match e.eq? with
  | some (_, v, .fvar y) => some (v, .fvar y)
  | _ => none

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

namespace Lean.Meta

abbrev ArrM := BaseM

namespace Arr

open Lean Elab Tactic

def applyRIntro1s (mv : MVarId) : ArrM MVarId := do
  let mut mv := mv
  for fv in (← mv.getDecl).lctx.getFVarIds do
    mv ← applyRIntro1 mv fv
  return mv
where
  applyRIntro1 (mv : MVarId) (fv : FVarId) : ArrM MVarId := mv.withContext do
    if (← fv.getType).eqWrite? matches some _ then
      let p ← Meta.mkAppM ``A.r_intro1 #[.fvar fv]
      let t ← Meta.inferType p
      let (_, mv) ← (← mv.assert (← Base.newHypName) t p).intro1P
      return (← (← mv.assert (← Base.newHypName) t p).intro1P).snd
    return mv

abbrev CacheList := List (Expr × Expr × Expr × Expr)

def applyRIntro2 (mv : MVarId) (fv1 : FVarId) (fv2 : FVarId) (fv3 : FVarId) : StateT CacheList ArrM (List MVarId) := mv.withContext do
  match (← fv1.getType).eq?, (← fv2.getType).eqWrite?, (← fv3.getType).eqRead? with
  | some (_, d, e), some (a, b, i, _), some (_, c, j) =>
    if (i != j) && (d == a || d == b) && e == c then
      if !(← get).contains (a, b, i, j) then
        modify ((a, b, i, j) :: (b, a, i, j) :: ·)
        let eq1 ← Meta.mkAppM ``Eq #[a, c]
        let eq2 ← Meta.mkAppM ``Eq #[b, c]
        let mut omv := (← Meta.mkFreshExprMVar (← Meta.mkAppM ``Or #[eq1, eq2])).mvarId!
        let p ← Meta.mkAppM ``A.r_intro2 #[.mvar omv, .fvar fv2, .fvar fv3]
        let t ← Meta.inferType p
        let (fv, mv) ← (← mv.assert (← Base.newHypName) t p).intro1P
        omv := (← omv.apply (mkConst (if d == a then ``Or.inl else ``Or.inr)))[0]!
        omv.assign (.fvar fv1)
        let #[sg1, sg2] ← mv.cases fv #[⟨false, [← Base.newHypName]⟩, ⟨false, [← Base.newHypName]⟩] |
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
  findFVOrCreate (mv : MVarId) (e : Expr) : ArrM (FVarId × FVarId × MVarId) := mv.withContext do
    for fv in (← mv.getDecl).lctx.getFVarIds do
      if let some (_, x, e') := (← fv.getType).eq? then
        if e' == e then
          return (x.fvarId!, fv, mv)
    let (x, mv) ← (← mv.assertExt (← Base.newVarName) (← Meta.inferType e) e).intro1P
    let (fv, mv) ← mv.intro1P
    return (x, fv, mv)
  replaceLHS (mv : MVarId) (fv : FVarId) : ArrM (FVarId × FVarId × FVarId × MVarId) := mv.withContext do
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
  replaceRHS (mv : MVarId) (fv : FVarId) : ArrM (FVarId × FVarId × FVarId × MVarId) := mv.withContext do
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

def product (xs : List α) (ys : List β) : List (α × β) :=
  (xs.map (fun x => ys.map (fun y => (x, y)))).join

partial def applyRIntro2s (cache : CacheList) (mv : MVarId) : ArrM (List MVarId) := do
  let fvs := (← mv.getDecl).lctx.getFVarIds.toList
  let eqFVs ← mv.withContext (eqFVs fvs)
  let eqReads ← mv.withContext (eqReads fvs)
  let eqWrites ← mv.withContext (eqWrites fvs)
  let mut mvs := []
  let mut cache := cache
  for (fv1, fv2, fv3) in product eqFVs (product eqWrites eqReads) do
    (mvs, cache) ← StateT.run (applyRIntro2 mv fv1 fv2 fv3) cache
    if !mvs.isEmpty then
      break
  if mvs.isEmpty then
    return [mv]
  else
    return (← applyRIntro2s cache mvs[0]!) ++ (← applyRIntro2s cache mvs[1]!)
where
  eqFVs (fvs : List FVarId) := fvs.filterM (fun fv => return (← fv.getType).eqFV?.toBool)
  eqReads (fvs : List FVarId) := fvs.filterM (fun fv => return (← fv.getType).eqRead?.toBool)
  eqWrites (fvs : List FVarId) := fvs.filterM (fun fv => return (← fv.getType).eqWrite?.toBool)

def applyExt (mv : MVarId) (fv : FVarId) : ArrM MVarId := mv.withContext do
  if (← fv.getType).ne? matches some _ then
    let p ← Meta.mkAppM ``A.ext #[.fvar fv]
    let t ← Meta.inferType p
    let mut (fv, mv) ← (← mv.assert (← Base.newHypName) t p).intro1P
    (_, fv, mv) ← introExists mv fv
    (_, _, fv, mv) ← replaceLHS mv fv
    (_, _, fv, mv) ← replaceRHS mv fv
    return mv
  return mv
where
  introExists (mv : MVarId) (fv : FVarId) : ArrM (FVarId × FVarId × MVarId) := do
    let #[sg] ← mv.cases fv #[⟨false, [← Base.newVarName, ← Base.newHypName]⟩] | throwError "exists intro failed."
    return (sg.fields[0]!.fvarId!, sg.fields[1]!.fvarId!, sg.mvarId)
  replaceLHS (mv : MVarId) (fv : FVarId) : ArrM (FVarId × FVarId × FVarId × MVarId) := do
    let some (_, lhs, rhs) := (← mv.withContext fv.getType).ne? | throwError "replacing LHS of {Expr.fvar fv} failed."
    let (x, mv) ← (← mv.assertExt (← Base.newVarName) (← Meta.inferType lhs) lhs).intro1P
    let (xfv, mv) ← mv.intro1P
    mv.withContext do
    let xt ← Meta.mkAppM ``Ne #[.fvar x, rhs]
    let xmv := (← Meta.mkFreshExprMVar (← Meta.mkAppM ``Eq #[← fv.getType, xt])).mvarId!
    let ⟨fv, mv, _⟩ ← mv.replaceLocalDecl fv xt (.mvar xmv)
    let r ← xmv.rewrite (← xmv.getType) (.fvar xfv)
    let xmv ← xmv.replaceTargetEq r.eNew r.eqProof
    xmv.refl
    return (x, xfv, fv, mv)
  replaceRHS (mv : MVarId) (fv : FVarId) : ArrM (FVarId × FVarId × FVarId × MVarId) := do
    let some (_, lhs, rhs) := (← mv.withContext fv.getType).ne? | throwError "replacing RHS of {Expr.fvar fv} failed."
    let (y, mv) ← (← mv.assertExt (← Base.newVarName) (← Meta.inferType rhs) rhs).intro1P
    let (yfv, mv) ← mv.intro1P
    mv.withContext do
    let yt ← Meta.mkAppM ``Ne #[lhs, .fvar y]
    let ymv := (← Meta.mkFreshExprMVar (← Meta.mkAppM ``Eq #[← fv.getType, yt])).mvarId!
    let ⟨fv, mv, _⟩ ← mv.replaceLocalDecl fv yt (.mvar ymv)
    let r ← ymv.rewrite (← ymv.getType) (.fvar yfv)
    let ymv ← ymv.replaceTargetEq r.eNew r.eqProof
    ymv.refl
    return (y, yfv, fv, mv)

def applyExts (mv : MVarId) : ArrM MVarId := do
  let mut mv := mv
  for fv in (← mv.getDecl).lctx.getFVarIds do
    mv ← applyExt mv fv
  return mv

def arrClosure (mv : MVarId) : ArrM (List MVarId) := do
  let mv ← (EUF.congrClosure mv).run' { }
  let mv ← applyExts mv
  let mv ← applyRIntro1s mv
  let mvs' ← applyRIntro2s [] mv
  let mut mvs := []
  for mv' in mvs' do
    let mv ← (EUF.congrClosure mv').run' { }
    mvs := mv :: mvs
  return mvs

end Arr

def arrClosure (mv : MVarId) : MetaM (List MVarId) := (Arr.arrClosure mv).run' { mv := mv }

private def newHypName (mv : MVarId) : MetaM Name := do
  return Lean.LocalContext.getUnusedName (← mv.getDecl).lctx `hds








def flat (mv : MVarId) (fv : FVarId) : MetaM MVarId := mv.withContext do
  let some (_, lhs, rhs) := (← fv.getType).eq? | throwError "something went wrong..."
  logInfo m!"LHS := {lhs}"
  logInfo m!"RHS := {rhs}"
  
-- where
--   findFVOrCreate (mv : MVarId) (e : Expr) : ArrM (FVarId × FVarId × MVarId) := mv.withContext do
--     for t in e.getAppArgs do
--       let (x, mv) ← (← mv.assertExt (← Base.newVarName) (← Meta.inferType t) t).intro1P
--       let (fv, mv) ← mv.intro1P
--       return (x, fv, mv)
--   replaceLHS (mv : MVarId) (fv : FVarId) : ArrM (FVarId × FVarId × FVarId × MVarId) := mv.withContext do
--     let some (_, lhs, rhs) := (← fv.getType).eq? | throwError "something went wrong..."
--     let (x, xfv, mv) ← findFVOrCreate mv lhs
--     mv.withContext do
--     let xt ← Meta.mkAppM ``Eq #[.fvar x, rhs]
--     let xmv := (← Meta.mkFreshExprMVar (← Meta.mkAppM ``Eq #[← fv.getType, xt])).mvarId!
--     let ⟨fv, mv, _⟩ ← mv.replaceLocalDecl fv xt (.mvar xmv)
--     let r ← xmv.rewrite (← xmv.getType) (.fvar xfv)
--     let xmv ← xmv.replaceTargetEq r.eNew r.eqProof
--     xmv.refl
--     return (x, xfv, fv, mv)
  
-- where
--   loop (mv : MVarId) (e : Expr) : MVarId := mv.withContext do
--     for t in e.getAppArgs do
--       if t.isApp then
--         let (x, mv) ← (← mv.assertExt (← Base.newVarName) (← Meta.inferType t) t).intro1P
--         let (fv, mv) ← mv.intro1P
--         let ⟨fv, mv, _⟩ ← mv.replaceLocalDecl fv xt (.mvar xmv)
--         let r ← xmv.rewrite (← xmv.getType) (.fvar xfv)
--         return loop mv
--       else
--         return _
        

--         return mv




  let mut current_lhs := lhs
  let mut next := lhs.getAppArgs[0]!
  while current_lhs.isApp do
    let ar := current_lhs.getAppArgs
    for t in ar do
      current_lhs := t
    
      logInfo m! "{current_lhs}"
      
    




  
  
  
    
  return mv
  





syntax (name := arr) "arr" : tactic

open Elab Tactic in
@[tactic arr] def evalArr : Tactic := fun _ => do
  let mut mv ← Tactic.getMainGoal
  while (← mv.getType).isArrow do
    (_, mv) ← mv.intro (← newHypName mv)
  -- let mvs' ← arrClosure mv
  -- let mut mvs := []
  -- for mv' in mvs' do
  --   try
  --     mv'.contradiction
  --   catch _ =>
  --     mvs := mv' :: mvs
  -- Tactic.replaceMainGoal mvs
  for fv in (← mv.getDecl).lctx.getFVarIds do
    mv.withContext do
    logInfo m!"{Expr.fvar fv}" 
  logInfo m!"Array size {Lean.mkNatLit (← mv.getDecl).lctx.getFVarIds.size}"
  mv ← flat mv (← mv.getDecl).lctx.getFVarIds[9]!
  Tactic.replaceMainGoal [mv]
end Lean.Meta
