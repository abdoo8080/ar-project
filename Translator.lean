import Sexp

def translateTerm : Sexp → String
  | sexp!{(= {e₁} {e₂})} => s!"({translateTerm e₁}) = ({translateTerm e₂})"
  | sexp!{(distinct {e₁} {e₂})}
  | sexp!{(not (= {e₁} {e₂}))} => s!"({translateTerm e₁}) ≠ ({translateTerm e₂})"
  | sexp!{(store {a} {i} {v})} => s!"({translateTerm a}).write {i} ({translateTerm v})"
  | sexp!{(select {a} {i})} => s!"({translateTerm a}).read {i}"
  | sexp!{(and {p} {q})} => s!"{translateTerm p} → {translateTerm q}"
  | .atom s => s
  | _ => ""

def translateCommand : Sexp → String
  | sexp!{(declare-const {a} A)} => s!"{a}"
  | sexp!{(declare-fun {a} () A)} => "{" ++ s!"{a} : A I E" ++ "}"
  | sexp!{(assert {e})} => translateTerm e
  | _ => ""

def translateQuery (q : String) : String := Id.run do
  let .ok cmds := Sexp.parseMany q | panic! "translation failed."
  let (asserts, decls) := cmds.partition (· matches sexp!{(assert {_})})
  let decls := (decls.map translateCommand).filter (· ≠ "")
  let asserts := asserts.map translateCommand
  let lq := s!"import LMT

variable \{I} [Nonempty I] \{E} [Nonempty E] [Nonempty (A I E)]

example \{{String.intercalate " " decls} : A I E} :
        {String.intercalate " → " asserts} → False := by
  arr"
  return lq

open System in
def main (args : List String) : IO Unit := do
  let path := args[0]!
  let query ← IO.FS.readFile ⟨path⟩
  IO.println (translateQuery query)
