import LMT

variable {I} [Nonempty I] {E} [Nonempty E] [Nonempty (A I E)]

example {a1 a2 a3 : A I E} :
        ((a3).write i1 (v3)) = (a3) → ((a3).read i1) ≠ (v3) → False := by
  arr
