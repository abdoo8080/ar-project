import A

variable {I} [Nonempty I] {E} [Nonempty E] [Nonempty (A I E)]

theorem t {a : A I E} : (a.write i v₂).read i = v₁ ↔ v₁ = v₂ := by
  rw [a1]
  apply Iff.intro <;> intro h <;> exact Eq.symm h

theorem t' {a : A I E} : (a.write i v₂).read i = v₁ ↔ v₁ = v₂ :=
  a1 (a := a) ▸ ⟨(· ▸ rfl), (· ▸ rfl)⟩

/-

(a.write i v₂).read i = v₁ ↔ v₁ = v₂
((a.write i v₂).read i = v₁ → v₁ = v₂) ∧ (v₁ = v₂ → (a.write i v₂).read i = v₁)
(¬(a.write i v₂).read i = v₁ ∨ v₁ = v₂) ∧ (¬(v₁ = v₂) ∨ (a.write i v₂).read i = v₁)



-/

theorem t'' {a : A I E} : (¬((a.write i v₂).read i = v₁) ∨ v₁ = v₂) ∧ (¬(v₁ = v₂) ∨ (a.write i v₂).read i = v₁) → False := by
  arr
  sorry
