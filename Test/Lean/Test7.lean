import LMT

variable {I} [Nonempty I] {E} [Nonempty E] [Nonempty (A I E)]

example {a1 a2 a3 : A I E} :
        (v2) ≠ ((((a1).write i1 (v2)).write i2 (v2)).read i1) → False := by
  arr
