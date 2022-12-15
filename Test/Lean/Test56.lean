import LMT

variable {I} [Nonempty I] {E} [Nonempty E] [Nonempty (A I E)]

example {a1 a2 a3 : A I E} :
        ((a1).read i1) ≠ (((((a1).write i2 ((a2).read i3)).write i3 ((a1).read i1)).write i1 ((a1).read i1)).read i3) → False := by
  arr
