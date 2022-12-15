import LMT

variable {I} [Nonempty I] {E} [Nonempty E] [Nonempty (A I E)]

example {a1 a2 a3 : A I E} :
        (v1) ≠ ((((a2).write i2 (v1)).write i3 (v1)).read i2) → False := by
  arr
