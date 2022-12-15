import LMT

variable {I} [Nonempty I] {E} [Nonempty E] [Nonempty (A I E)]

example {a1 a2 a3 : A I E} :
        ((a2).write i2 (v3)) ≠ (a2) → ((a1).write i2 (v3)) = (a2) → False := by
  arr
