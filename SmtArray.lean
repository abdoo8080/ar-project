opaque A : (I : Sort u₁) → (E : Sort u₂) → Sort (max u₁ u₂)

variable {I} [Nonempty I] {E} [Nonempty E] [Nonempty (A I E)]

noncomputable opaque A.read : A I E → I → E

noncomputable opaque A.write : A I E → I → E → A I E

axiom a1 : ∀ {a : A I E}, ∀ {i : I}, ∀ {v : E}, (a.write i v).read i = v

axiom a2 : ∀ {a : A I E}, ∀ {i j : I}, ∀ {v : E}, i ≠ j → (a.write i v).read j = a.read j

axiom a3 : ∀ {a b : A I E}, (∀ i : I, a.read i = b.read i) → a = b

theorem t {a : A I E} : (a.write i v₂).read i = v₁ ↔ v₁ = v₂ := by
  rw [a1]
  apply Iff.intro <;> intro h <;> exact Eq.symm h

theorem t' {a : A I E} : (a.write i v₂).read i = v₁ ↔ v₁ = v₂ :=
  a1 (a := a) ▸ ⟨(· ▸ rfl), (· ▸ rfl)⟩
