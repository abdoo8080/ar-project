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

def apply_r_intro1 (cs : List Expr) : List Expr := _

def purify (cs : List Expr) : List Expr := _

def saturate (cs : List Expr) : List Expr := _

def solve (cs : List Expr) : Either Expr (List (Name × Expr)) := _

@[tactic arr] def evalArr : Tactic := fun _ => Tactic.withMainContext do
  let goalType ← Tactic.getMainTarget
  logInfo m!"goal: {goalType}"

end Solver
