import A.A
import Lean

open Lean Elab Tactic

initialize
  Lean.registerTraceClass `arr.debug

inductive Either (α β) where
  | left : α → Either α β
  | right : β → Either α β

namespace Solver

structure State where
  lits : List Expr := []

abbrev SolverM := StateT State MetaM

syntax (name := arr) "arr" : tactic

example : True := by
  have : True := True.intro
  simp



def decompose (cs : Expr) : SolverM Unit := do
  return

def newHypName (mv : MVarId) : MetaM Name := do
  return Lean.LocalContext.getUnusedName (← mv.getDecl).lctx `h

def newVarName (mv : MVarId) : MetaM Name := do
  return Lean.LocalContext.getUnusedName (← mv.getDecl).lctx `x

def newMVarName (mv : MVarId) : MetaM Name := do
  return Lean.LocalContext.getUnusedName (← mv.getDecl).lctx `m

def applyRIntros (mv : MVarId) : MetaM MVarId := do
  let mut mv := mv
  for fv in (← mv.getDecl).lctx.getFVarIds do
    mv ← applyRIntro mv fv
  return mv
where
  applyRIntro (mv : MVarId) (fv : FVarId) : MetaM MVarId := mv.withContext do
    match ← fv.getType with
    | (.app (.app (.app (.const ``Eq _) _) _)
            (.app (.app (.app (.app (.app (.app (.const ``A.write _) _) _) _) _) _) _)) =>
      let p ← Meta.mkAppM ``A.r_intro1 #[.fvar fv]
      let t ← Meta.inferType p
      let (_, mv) ← (← mv.assert (← newHypName mv) t p).intro1P
      return mv
    | _ => return mv

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
    _ ← xmv.refl
    logInfo m!"xmv: {← xmv.isAssigned}"
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
    _ ← ymv.refl
    logInfo m!"ymv: {← ymv.isAssigned}"
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

def purify (cs : List Expr) : List Expr := sorry

def saturate (cs : List Expr) : List Expr := sorry

def solve (cs : List Expr) : Either Expr (List (Name × Expr)) := sorry

@[tactic arr] def evalArr : Tactic := fun _ => do
  let mut mv ← Tactic.getMainGoal
  while (← mv.getType).isArrow do
    (_, mv) ← mv.intro (← newHypName mv)
  -- goal ← apply_ext goal
  -- Tactic.replaceMainGoal [goal]
  -- goal.contradictiond
  mv ← applyExts mv
  -- mv ← applyRIntros mv
  Tactic.replaceMainGoal [mv]
  -- for h in hs' do
  --   logInfo m!"h : {h}"
  -- let (fv, mv) ← (← goal.define (← newVarName goal) (← Lean.Meta.inferType (Lean.mkNatLit 1)) (Lean.mkNatLit 1)).intro1P
  -- goal := mv
  -- Tactic.replaceMainGoal [mv]
  -- let t ← Meta.mkAppM `Eq #[Lean.mkNatLit 1, Lean.mkNatLit 1]
  -- let (_, mv) ← (← goal.assert (← newHypName goal) t (mkConst `rfl)).intro1P
  -- Tactic.replaceMainGoal [mv]

-- let (_, mvarId) ← (← mvarId.assert conc.nmEqBody tpEqBody pfEqBody).intro1P
-- let (fv, mvarId) ← (← mvarId.define nm (← inferType eBody) eBody).intro1P

end Solver
