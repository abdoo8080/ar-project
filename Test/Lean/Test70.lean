import LMT

variable {I} [Nonempty I] {E} [Nonempty E] [Nonempty (A I E)]

example {a1 a2 a3 : A I E} :
        (v3) = ((a2).read i1) → ((a2).write i1 (v3)) ≠ (a2) → False := by
  arr
