import LMT

variable {I} [Nonempty I] {E} [Nonempty E] [Nonempty (A I E)]

example {a1 a2 a3 : A I E} :
        ((a3).write i1 ((a2).read i2)) = (a1) → ((a1).read i1) ≠ ((a2).read i2) → False := by
  arr
