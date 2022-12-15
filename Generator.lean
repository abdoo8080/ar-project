import Sexp

def prelude :=
"(set-logic AX)

(declare-sort I 0)
(declare-sort E 0)

(define-sort A () (Array I E))

(declare-const a1 A)
(declare-const a2 A)
(declare-const a3 A)

(declare-const i1 I)
(declare-const i2 I)
(declare-const i3 I)

(declare-const v1 E)
(declare-const v2 E)
(declare-const v3 E)

"

def epilogue := "

(check-sat)
"

def pre := "(define-fun f ((a1 (Array I E)) (a2 (Array I E)) (a3 (Array I E)) (i1 I) (i2 I) (i3 I) (v1 E) (v2 E) (v3 E)) Bool "

def suf := ")"

def generateBenchmark (a : String) : String := prelude ++ s!"(assert {a})" ++ epilogue

open System in
def main (args : List String) : IO Unit := do
  let path := args[0]!
  let lines ← IO.FS.lines ⟨path⟩
  let i := pre.length
  let j := suf.length
  let asserts := lines.map fun s => s.extract ⟨i⟩ (s.endPos - ⟨j⟩)
  let mut c := 1
  for assert in asserts do
    IO.FS.writeFile (((FilePath.mk "Test").join "SMT").join s!"test{c}.smt2") (generateBenchmark assert)
    c := c + 1
