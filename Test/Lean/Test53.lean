import LMT

variable {I} [Nonempty I] {E} [Nonempty E] [Nonempty (A I E)]

example {a1 a2 a3 : A I E} :
        ((((a2).write i1 (v1)).write i2 (v1)).read i1) ≠ (v1) → False := by
  arr
