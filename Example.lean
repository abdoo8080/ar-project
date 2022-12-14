import LMT

variable {I} [Nonempty I] {E} [Nonempty E] [Nonempty (A I E)]

example {a a' b b' : A I E} : a.write i (b.read i) = b.write i (a.read i) → a ≠ b → False := by
  arr
