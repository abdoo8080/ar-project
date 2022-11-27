opaque A : (I : Sort u₁) → (E : Sort u₂) → Sort (max u₁ u₂)

namespace A

variable {I} [Nonempty I] {E} [Nonempty E] [Nonempty (A I E)]

noncomputable opaque read : A I E → I → E

noncomputable opaque write : A I E → I → E → A I E

axiom rw1 : ∀ {a : A I E}, ∀ {i : I}, ∀ {v : E}, (a.write i v).read i = v

axiom rw2 : ∀ {a : A I E}, ∀ {i j : I}, ∀ {v : E}, i ≠ j → (a.write i v).read j = a.read j

axiom ex : ∀ {a b : A I E}, (∀ i : I, a.read i = b.read i) → a = b

theorem contrapositive : (p → q) → ¬q → ¬p := fun hpq hnq hp => hnq (hpq hp)

theorem forall_eq_not_exists_not {p : α → Prop} : (∀ x, p x) = ¬ ∃ x, ¬ p x :=
  propext ⟨fun hfxpx ⟨x, hnpx⟩ => hnpx (hfxpx x),
          fun henxnpx x => match Classical.em (p x) with
            | Or.inl hpx  => hpx
            | Or.inr hnpx => absurd ⟨x, hnpx⟩ henxnpx⟩

theorem double_neg : (¬¬p) = p := propext sorry

theorem r_intro1 {a b : A I E}: a = b.write i v → v = a.read i := sorry

theorem r_intro2 {a b c : A I E} : a = c ∨ b = c → a = b.write i v → x = c.read j → i = j ∨ a.read j = b.read j := sorry

theorem ext {a b : A I E} : a ≠ b → ∃i, a.read i ≠ b.read i := fun hne =>
  double_neg (p := ∃ i, read a i ≠ read b i) ▸
  forall_eq_not_exists_not (p := (λ i => a.read i = b.read i)) ▸
  (contrapositive ex) hne

example {a b : A I E} : a.write i (b.read i) = b.write i (a.read i) → a ≠ b → False := fun h0 h6 =>
  let v := b.read i
  have h3 : v = b.read i := rfl
  let w := a.read i
  have h4 : w = a.read i := rfl
  let a' := a.write i v
  have h1 : a' = a.write i v := rfl
  let b' := b.write i w
  have h2 : b' = b.write i w := rfl
  have h5 : a' = b' := h1 ▸ h2 ▸ h3 ▸ h4 ▸ h0
  lem h1 h2 h3 h4 h5 h6
where
  lem {a a' b b' : A I E} {v w : E} : a' = a.write i v → b' = b.write i w → v = b.read i → w = a.read i → a' = b' → a ≠ b → False :=
    fun h1 h2 h3 h4 h5 h6 =>
      have ⟨k, h9⟩ : ∃i, a.read i ≠ b.read i := ext h6
      let x := read a k
      have h7 : x = read a k := rfl
      let y := read b k
      have h8 : y = read b k := rfl
      have h9 : x ≠ y := h7 ▸ h8 ▸ h9
      have h10 : i = k ∨ a'.read k = a.read k := r_intro2 (Or.inr rfl) h1 h7
      match h10 with
      | Or.inl h10 =>
        have h11 : x = w := h4 ▸ h10 ▸ h7
        have h12 : v = y := h3 ▸ h10 ▸ h8
        have h13 : v = a'.read i := r_intro1 h1
        have h14 : w = b'.read i := r_intro1 h2
        have h15 : w = v := h13 ▸ h5 ▸ h14
        have h16 : x = y := h11 ▸ h12 ▸ h15
        h9 h16
      | Or.inr h10 =>
        let x' := a'.read k
        have h11 : x' = a'.read k := rfl
        have h10 : x = x' := h7 ▸ h11 ▸ h10 ▸ rfl
        have h12 : i = k ∨ b'.read k = b.read k := r_intro2 (Or.inr rfl) h2 h8
        match h12 with
        | Or.inl h12 =>
          have h13 : x = w := h4 ▸ h12 ▸ h7
          have h14 : v = y := h3 ▸ h12 ▸ h8
          have h15 : v = a'.read i := r_intro1 h1
          have h16 : w = b'.read i := r_intro1 h2
          have h17 : w = v := h15 ▸ h5 ▸ h16
          have h18 : x = y := h13 ▸ h14 ▸ h17
          h9 h18
        | Or.inr h12 =>
          let y' := b'.read k
          have h13 : y' = b'.read k := rfl
          have h14 : y' = y := h8 ▸ h12 ▸ h13
          have h15 : x' = y' := h11 ▸ h13 ▸ h5 ▸ rfl
          have h16 : x = y := h10 ▸ h14 ▸ h15
          h9 h16

end A
