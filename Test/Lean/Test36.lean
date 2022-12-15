import LMT

variable {I} [Nonempty I] {E} [Nonempty E] [Nonempty (A I E)]

example {a1 a2 a3 : A I E} :
        ((a1).read i2) ≠ (((a1).write i1 ((a1).read i2)).read i2) → False := by
  arr
