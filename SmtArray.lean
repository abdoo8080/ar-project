opaque A : (I : Sort u₁) → (E : Sort u₂) → Sort (max u₁ u₂)

variable {I : Sort u₁} [Inhabited I] {E : Sort u₂} [Inhabited E] [Inhabited (A I E)]

opaque A.read : A I E → I → E

opaque A.write : A I E → I → E → A I E

axiom a1 : ∀ a : A I E, ∀ i : I, ∀ v : E, (a.write i v).read i = v

axiom a2 : ∀ a : A I E, ∀ i j : I, ∀ v : E, i ≠ j → (a.write i v).read j = a.read j

axiom a3 : ∀ a b : A I E, (∀ i : I, a.read i = b.read i) → a = b

def hello := "world"

theorem t {a : A I E} : a.read i = v₁ → (a.write i v₂).read i = v₁ ↔ v₁ = v₂ := sorry
