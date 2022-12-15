import LMT

variable {I} [Nonempty I] {E} [Nonempty E] [Nonempty (A I E)]

example {a1 a2 a3 : A I E} :
        (i1) = (i2) → ((((a2).write i3 (v2)).write i1 (v2)).read i3) ≠ (v2) → False := by
  arr
