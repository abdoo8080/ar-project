import LMT

variable {I} [Nonempty I] {E} [Nonempty E] [Nonempty (A I E)]

example {a1 a2 a3 : A I E} :
        ((((a2).write i3 (v3)).write i2 (v3)).read i3) ≠ (v3) → False := by
  arr
