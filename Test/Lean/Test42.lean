import LMT

variable {I} [Nonempty I] {E} [Nonempty E] [Nonempty (A I E)]

example {a1 a2 a3 : A I E} :
        ((a2).read i2) ≠ (((a2).write i1 ((a2).read i2)).read i2) → False := by
  arr