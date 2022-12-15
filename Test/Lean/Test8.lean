import LMT

variable {I} [Nonempty I] {E} [Nonempty E] [Nonempty (A I E)]

example {a1 a2 a3 : A I E} :
        ((a3).read i2) ≠ (((a3).write i1 ((a3).read i2)).read i2) → False := by
  arr
