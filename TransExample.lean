import Lean
import Sexp

open Lean

def test := "
(declare-fun a1 () (Array Index Element))
(declare-fun i0 () Index)
(declare-fun i1 () Index)
(assert (not (= (store (store (store (store a1 i0 (select a1 i1)) i1 (select a1 i0)) i1 (select (store (store a1 i0 (select a1 i1)) i1 (select a1 i0)) i1)) i1 (select (store (store a1 i0 (select a1 i1)) i1 (select a1 i0)) i1)) (store (store (store (store a1 i1 (select a1 i0)) i0 (select a1 i1)) i1 (select (store (store a1 i1 (select a1 i0)) i0 (select a1 i1)) i0)) i0 (select (store (store a1 i1 (select a1 i0)) i0 (select a1 i1)) i1)))))
"

#eval Sexp.expr (Sexp.parseMany test).toOption.get!

def translateTerm : Sexp → String
  | sexp!{(not (= {e₁} {e₂}))} => s!"({translateTerm e₁}) ≠ ({translateTerm e₂})"
  | sexp!{(not {e})} => s!"¬({translateTerm e})"
  | sexp!{(= {e₁} {e₂})} => s!"({translateTerm e₁}) = ({translateTerm e₂})"
  | sexp!{(store {a} {i} {v})} => s!"({translateTerm a}).write {i} ({translateTerm v})"
  | sexp!{(select {a} {i})} => s!"({translateTerm a}).read {i}"
  | .atom s => s
  | _ => ""

def translateCommand : Sexp → String
  | sexp!{(declare-fun {a} () (Array {_} {_}))} => "{" ++ s!"{a} : A I E" ++ "}"
  | sexp!{(assert {e})} => translateTerm e
  | _ => ""

def translateQuery (q : String) : String := Id.run do
  let .ok cmds := Sexp.parseMany q | panic! "asdf"
  let (asserts, decls)  : List Sexp × List Sexp:= cmds.partition (· matches sexp!{(assert {_})})
  let ex := s!"example {intercalate decls " " translateCommand} :
        {intercalate asserts " → " translateCommand} := by
  arr"
  return ex
where
  intercalate e s f := s!"{String.intercalate s (e.map f)}"

#eval translateQuery test

def parseQuery : MetaM Expr := do
  return mkConst `False

def main : IO Unit := do
  -- ReaderT.run parseQuery {}
  return

#eval parseQuery
