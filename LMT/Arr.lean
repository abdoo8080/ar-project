import LMT.A
import LMT.Base
import LMT.EUF
import Lean

namespace Lean.Expr

/-- Is `e` an equality or a disequality? -/
@[inline] def eqne? (e : Expr) : Option (Expr × Expr × Expr) :=
  match e.eq? with
  | some (t, lhs, rhs) => some (t, lhs, rhs)
  | _ => match e.ne? with
    | some (t, lhs, rhs) => some (t, lhs, rhs)
    | _ => none

/-- Is `e` an equality with a free variable in the rhs? -/
@[inline] def eqFV? (e : Expr) : Option (Expr × Expr × Expr) :=
  match e.eq? with
  | some (t, v, .fvar y) => some (t, v, .fvar y)
  | _ => none

/-- Is `e` a `read`? -/
@[inline] def read? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity `A.read 5 then
    some (e.getArg! 3, e.getArg! 4)
  else
    none

/-- Is `e` a `write`? -/
@[inline] def write? (e : Expr) : Option (Expr × Expr × Expr) :=
  if e.isAppOfArity `A.write 6 then
    some (e.getArg! 3, e.getArg! 4, e.getArg! 5)
  else
    none

/-- Is `e` an equality with a `read` in the rhs? -/
@[inline] def eqRead? (e : Expr) : Option (Expr × Expr × Expr) :=
  match e.eq? with
  | some (_, v, e) => match e.read? with
    | some (a, i) => some (v, a, i)
    | _ => none
  | _ => none

/-- Is `e` an equality with a `write` in the rhs? -/
@[inline] def eqWrite? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
  match e.eq? with
  | some (_, a, e) => match e.write? with
    | some (b, i, v) => some (a, b, i, v)
    | _ => none
  | _ => none

end Lean.Expr

namespace Lean.Meta

/-- The Array monad. -/
abbrev ArrM := BaseM

namespace Arr

open Lean Elab Tactic

/-- Implements `RIntro1` rule. -/
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

abbrev Cache := HashSet (Expr × Expr × Expr × Expr)

/-- Implements `RIntro2` rule. -/
def applyRIntro2 (mv : MVarId) (fv1 : FVarId) (fv2 : FVarId) (fv3 : FVarId) : StateT Cache ArrM (List MVarId) := mv.withContext do
  match (← fv1.getType).eq?, (← fv2.getType).eqWrite?, (← fv3.getType).eqRead? with
  | some (_, d, e), some (a, b, i, _), some (_, c, j) =>
    if (i != j) && (d == a || d == b) && e == c then
      if !(← get).contains (a, b, i, j) then
        modify (·.insert (a, b, i, j) |>.insert (b, a, i, j))
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
    let some (_, lhs, _) := (← fv.getType).eq? | throwError "something went wrong..."
    let (x, xfv, mv) ← findFVOrCreate mv lhs
    mv.withContext do
    let r ← mv.rewrite (← fv.getType) (.fvar xfv) true (.pos [1])
    let ⟨fv, mv, _⟩ ← mv.replaceLocalDecl fv r.eNew r.eqProof
    return (x, xfv, fv, mv)
  replaceRHS (mv : MVarId) (fv : FVarId) : ArrM (FVarId × FVarId × FVarId × MVarId) := mv.withContext do
    let some (_, _, rhs) := (← fv.getType).eq? | throwError "something went wrong..."
    let (y, yfv, mv) ← findFVOrCreate mv rhs
    mv.withContext do
    let r ← mv.rewrite (← fv.getType) (.fvar yfv) true (.pos [1])
    let ⟨fv, mv, _⟩ ← mv.replaceLocalDecl fv r.eNew r.eqProof
    return (y, yfv, fv, mv)

/-- Returns the cross product of two lists. -/
def product (xs : List α) (ys : List β) : List (α × β) :=
  (xs.map (fun x => ys.map (fun y => (x, y)))).join

/-- Calls `RIntro2` multiple times. -/
partial def applyRIntro2s (cache : Cache) (mv : MVarId) : ArrM (List MVarId) := do
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
  eqFVs (fvs : List FVarId) := fvs.filterM fun fv => do
    return (← fv.getType).eqFV? >>= (·.fst.getAppFn) matches some (Expr.const ``A _)
  eqReads (fvs : List FVarId) := fvs.filterM (fun fv => return (← fv.getType).eqRead?.toBool)
  eqWrites (fvs : List FVarId) := fvs.filterM (fun fv => return (← fv.getType).eqWrite?.toBool)

/-- Implements `Ext` rule. -/
def applyExt (mv : MVarId) (fv : FVarId) : ArrM MVarId := mv.withContext do
  let some (Expr.const ``A _) := (← fv.getType).ne? >>= (·.fst.getAppFn) | return mv
  let p ← Meta.mkAppM ``A.ext #[.fvar fv]
  let t ← Meta.inferType p
  let mut (fv, mv) ← (← mv.assert (← Base.newHypName) t p).intro1P
  (_, fv, mv) ← introExists mv fv
  (_, _, fv, mv) ← replaceLHS mv fv
  (_, _, fv, mv) ← replaceRHS mv fv
  return mv
where
  introExists (mv : MVarId) (fv : FVarId) : ArrM (FVarId × FVarId × MVarId) := do
    let #[sg] ← mv.cases fv #[⟨false, [← Base.newVarName, ← Base.newHypName]⟩] | throwError "exists intro failed."
    return (sg.fields[0]!.fvarId!, sg.fields[1]!.fvarId!, sg.mvarId)
  replaceLHS (mv : MVarId) (fv : FVarId) : ArrM (FVarId × FVarId × FVarId × MVarId) := do
    let some (_, lhs, _) := (← mv.withContext fv.getType).ne? | throwError "replacing LHS of {Expr.fvar fv} failed."
    let (x, mv) ← (← mv.assertExt (← Base.newVarName) (← Meta.inferType lhs) lhs).intro1P
    let (xfv, mv) ← mv.intro1P
    mv.withContext do
    let r ← mv.rewrite (← fv.getType) (.fvar xfv) true (.pos [1])
    let ⟨fv, mv, _⟩ ← mv.replaceLocalDecl fv r.eNew r.eqProof
    return (x, xfv, fv, mv)
  replaceRHS (mv : MVarId) (fv : FVarId) : ArrM (FVarId × FVarId × FVarId × MVarId) := do
    let some (_, _, rhs) := (← mv.withContext fv.getType).ne? | throwError "replacing RHS of {Expr.fvar fv} failed."
    let (y, mv) ← (← mv.assertExt (← Base.newVarName) (← Meta.inferType rhs) rhs).intro1P
    let (yfv, mv) ← mv.intro1P
    mv.withContext do
    let r ← mv.rewrite (← fv.getType) (.fvar yfv) true (.pos [1])
    let ⟨fv, mv, _⟩ ← mv.replaceLocalDecl fv r.eNew r.eqProof
    return (y, yfv, fv, mv)

/-- Calls `Ext` multiple times. -/
def applyExts (mv : MVarId) : ArrM MVarId := do
  let mut mv := mv
  for fv in (← mv.getDecl).lctx.getFVarIds do
    mv ← applyExt mv fv
  return mv

/-- The "Array Closure" algorithm. -/
def arrClosure (mv : MVarId) : ArrM (List MVarId) := do
  let mv ← (EUF.congrClosure mv).run' { }
  let mv ← applyExts mv
  let mv ← applyRIntro1s mv
  let mvs' ← applyRIntro2s HashSet.empty mv
  let mut mvs := []
  for mv' in mvs' do
    let mv ← (EUF.congrClosure mv').run' { }
    mvs := mv :: mvs
  return mvs

end Arr

/-- Stateless version of "Array Closure" algorithm. -/
def arrClosure (mv : MVarId) : MetaM (List MVarId) := (Arr.arrClosure mv).run' { mv := mv }

/-- Utility to generate a new name for a hypothesis. -/
private def newHypName (mv : MVarId) : MetaM Name := do
  return Lean.LocalContext.getUnusedName (← mv.getDecl).lctx `hds

/-- Utility to generate a new name for a variable. -/
private def newVarName (mv : MVarId) : MetaM Name := do
  return Lean.LocalContext.getUnusedName (← mv.getDecl).lctx `x

/-- Utility for flattening hypothesis in the Proof context. -/
def flat (mv : MVarId) (fv : FVarId) : MetaM MVarId := mv.withContext do
  let fvt ← fv.getType
  if fvt.eqne?.isNone then
    return mv
  let (fv, mv) ← replaceLHS mv fv
  let (_, mv) ← if fvt.eq?.toBool then replaceRHSeq mv fv else replaceRHSne mv fv
  return mv
where
  findFV? (mv : MVarId) (e : Expr) : MetaM (Option (FVarId × FVarId × MVarId)) := mv.withContext do
    for fv in (← mv.getDecl).lctx.getFVarIds do
      if let some (_, x, e') := (← fv.getType).eq? then
        if e' == e then
          return some (x.fvarId!, fv, mv)
    return none
  findFVOrCreate (mv : MVarId) (e : Expr) : MetaM (FVarId × FVarId × MVarId) := mv.withContext do
    for fv in (← mv.getDecl).lctx.getFVarIds do
      if let some (_, x, e') := (← fv.getType).eq? then
        if e' == e then
          return (x.fvarId!, fv, mv)
    let (x, mv) ← (← mv.assertExt (← newVarName mv) (← Meta.inferType e) e).intro1P
    let (fv, mv) ← mv.intro1P
    return (x, fv, mv)
  replaceLHS (mv : MVarId) (fv : FVarId) : MetaM (FVarId × MVarId) := mv.withContext do
    let some (_, lhs, _) := (← fv.getType).eqne? | throwError "something went wrong..."
    if lhs.isFVar then
      return (fv, mv)
    let (_, xfv, mv) ← findFVOrCreate mv lhs
    mv.withContext do
    let r ← mv.rewrite (← fv.getType) (.fvar xfv) true (.pos [1])
    let ⟨fv, mv, _⟩ ← mv.replaceLocalDecl fv r.eNew r.eqProof
    return (fv, mv)
  replaceRHSne (mv : MVarId) (fv : FVarId) : MetaM (FVarId × MVarId) := mv.withContext do
    let some (_, _, rhs) := (← fv.getType).eqne? | throwError "something went wrong..."
    if rhs.isFVar then
      return (fv, mv)
    let (_, yfv, mv) ← findFVOrCreate mv rhs
    mv.withContext do
    let r ← mv.rewrite (← fv.getType) (.fvar yfv) true (.pos [1])
    let ⟨fv, mv, _⟩ ← mv.replaceLocalDecl fv r.eNew r.eqProof
    return (fv, mv)
  replaceRHSeq (mv : MVarId) (fv : FVarId) : MetaM (FVarId × MVarId) := mv.withContext do
    let some (_, _, rhs) := (← fv.getType).eq? | throwError "something went wrong..."
    if rhs.isFVar then
      return (fv, mv)
    if let some (_, yfv, mv) ← findFV? mv rhs then
      if yfv != fv then
        return ← mv.withContext do
        let r ← mv.rewrite (← fv.getType) (.fvar yfv) true (.pos [1])
        let ⟨fv, mv, _⟩ ← mv.replaceLocalDecl fv r.eNew r.eqProof
        return (fv, mv)
    if isAtom rhs then
      return (fv, mv)
    let args := rhs.getAppArgs
    let mut fv := fv
    let mut mv := mv
    for arg in args do
      if !arg.isApp then
        continue
      let (_, yfv, mv') ← findFVOrCreate mv arg
      mv := mv'
      (fv, mv) ← mv.withContext do
      let r ← mv.rewrite (← fv.getType) (.fvar yfv) true (.pos [1])
      let ⟨fv, mv, _⟩ ← mv.replaceLocalDecl fv r.eNew r.eqProof
      return (fv, mv)
    return (fv, mv)
  isAtom (e : Expr) : Bool := Id.run do
    if e.isFVar then
      return true
    if !e.isApp then
      return false
    let mut flag := true
    for arg in e.getAppArgs do
      if !arg.isFVar then
        flag := false
    return flag

/-- Calls `flat` to a fixed point. -/
def flats (mv : MVarId) : MetaM MVarId := do
  let mut i := 0
  let mut mv' := mv
  let mut mv := mv
  while i < (← mv.getDecl).lctx.getFVarIds.size do
    mv ← flat mv (← mv.getDecl).lctx.getFVarIds[i]!
    i := i + 1
    if mv' != mv then
      mv' := mv
      i := 0
  return mv

/-- The `arr` tactic runs the Arrays decision procedure on the current goal. -/
syntax (name := arr) "arr" : tactic

open Elab Tactic in
/-- Implementation of the `arr` tactic. -/
@[tactic arr] def evalArr : Tactic := fun _ => do
  let mut mv ← Tactic.getMainGoal
  while (← mv.getType).isArrow do
    (_, mv) ← mv.intro (← newHypName mv)
  mv ← flats mv
  let mvs' ← arrClosure mv
  let mut mvs := []
  for mv' in mvs' do
    try
      mv'.contradiction
    catch _ =>
      mvs := mv' :: mvs
  Tactic.replaceMainGoal mvs

end Lean.Meta
