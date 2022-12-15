import Lean

namespace Lean.Meta

open Lean

structure Base.State where
  /-- Original goal to close. -/
  mv : MVarId

abbrev BaseM := StateT Base.State MetaM

namespace Base

/-- Utility to generate a new name for a hypothesis. -/
def newHypName : BaseM Name :=
  return Lean.LocalContext.getUnusedName (← (← get).mv.getDecl).lctx `h

/-- Utility to generate a new name for a variable. -/
def newVarName : BaseM Name :=
  return Lean.LocalContext.getUnusedName (← (← get).mv.getDecl).lctx `x

end Base

end Lean.Meta
