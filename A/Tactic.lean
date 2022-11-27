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
  return Lean.LocalContext.getUnusedName (← mv.getDecl).lctx `u

def apply_r_intro1_aux (es : List (FVarId × Expr)) : MetaM (List (Expr × Expr)) := do match es with
  | [] => return []
  | (fv, (.app (.app (.app (.const ``Eq _) _) a)
         (.app (.app (.app (.app (.app (.app (.const ``A.write _) _) _) _) b) i) v)))
      :: es =>
    let e ← Meta.mkAppM ``Eq #[v, (← Meta.mkAppM ``A.read #[a, i])]
    return (e, ← Meta.mkAppM ``A.r_intro1 #[.fvar fv]) :: (← apply_r_intro1_aux es)
  | _ :: es => apply_r_intro1_aux es

def apply_r_intro1 (mv : MVarId) : MetaM MVarId := mv.withContext do
  let mut mv := mv
  let fvs := (← mv.getDecl).lctx.getFVarIds
  let hs ← fvs.mapM FVarId.getType
  let hs' ← apply_r_intro1_aux (fvs.zip hs).toList
  for (t, p) in hs' do
    (_, mv) ← (← mv.assert (← newHypName mv) t p).intro1P
  return mv

def apply_ext_aux (es : List (FVarId × Expr)) : MetaM (List Expr) := do match es with
  | [] => return []
  | (fv, (.app (.app (.app (.const ``Ne _) _) _) _)) :: es =>
    let e ← Meta.mkAppM ``A.ext #[.fvar fv]
    return e :: (← apply_ext_aux es)
  | _ :: es => apply_ext_aux es

def apply_ext (mv : MVarId) : MetaM MVarId := mv.withContext do
  let mut mv := mv
  let fvs := (← mv.getDecl).lctx.getFVarIds
  let hs ← fvs.mapM FVarId.getType
  let ps ← apply_ext_aux (fvs.zip hs).toList
  let mut fv := ⟨`h⟩
  for p in ps do
    let t ← Meta.inferType p
    (fv, mv) ← (← mv.assert (← newHypName mv) t p).intro1P
    let h : FVarId := ⟨← newHypName mv⟩
    let #[sg] ← mv.cases fv #[⟨false, [← newVarName mv, h.name]⟩] | throwError "Something went wrong..."
    mv := sg.mvarId
    -- (fv, mv) ← (← mv.assertExt (← newVarName mv) (← Meta.inferType (← getTypeLHS h mv)) (← getTypeLHS h mv)).intro1P
  return mv
where
  getTypeLHS (h : FVarId) (mv : MVarId) : MetaM Expr := mv.withContext do
    let ht ← h.getType
    let (.app (.app (.app (.const ``Ne _) lhs) _) _) := ht | throwError "Something went wrong..."
    return lhs

def purify (cs : List Expr) : List Expr := sorry

def saturate (cs : List Expr) : List Expr := sorry

def solve (cs : List Expr) : Either Expr (List (Name × Expr)) := sorry

@[tactic arr] def evalArr : Tactic := fun _ => do
  let mut goal ← Tactic.getMainGoal
  let mut hs := []
  while (← goal.getType).isArrow do
    let (fv, mv) ← goal.intro (← newHypName goal)
    hs := fv :: hs
    goal := mv
  goal ← apply_r_intro1 goal
  Tactic.replaceMainGoal [goal]
  goal ← apply_ext goal
  Tactic.replaceMainGoal [goal]
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
