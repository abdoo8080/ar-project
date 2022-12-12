import LMT

variable {I} [Nonempty I] {E} [Nonempty E] [Nonempty (A I E)]

example {a a' b b' : A I E} : a' = a.write i v → b' = b.write i w → v = b.read i → w = a.read i → a' = b' → a ≠ b → False := by
  arr
