import LMT

variable {I} [Nonempty I] {E} [Nonempty E] [Nonempty (A I E)]

example {a1 a2 a3 : A I E} :
        (v3) ≠ ((((a1).write i2 (v3)).write i3 (v3)).read i2) → False := by
  arr
