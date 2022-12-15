opaque Var : Type
opaque Val : Type

variable [DecidableEq Var] [Nonempty Val]

def I := Var → Val

def update (i : I) (x : Var) (v : Val) : Var → Val := fun k =>
  if x = k then v else i k

notation i "[" x " ↦ " v "]" => update i x v

inductive Atom where
  | var : Var → Atom
  | func : Var → List Var → Atom

inductive Formula where
  | atom : Atom → Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | imp : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | forall : Var → Formula → Formula
  | exists : Var → Formula → Formula

opaque Models : I → Formula → Prop
opaque NotModels : I → Formula → Prop

axiom Models.not {i a} : NotModels i (.not a) → Models i a
axiom Models.forall {i x a} : Models i (.forall x a) → (∀ v, Models (i[x ↦ v]) a)
axiom Models.exists {i x a} : Models i (.exists x a) → (v : Val) → Models (i[x ↦ v]) a

axiom NotModels.not  {i a} : Models i (.not a) → NotModels i a
axiom NotModels.exists {i x a} : NotModels i (.exists x a) → (∀ v, Models (i[x ↦ v]) a)

notation i " ⊨ " a => Models i a
notation i " ⊭ " a => NotModels i a

-- axiom Models.imp {}

theorem t {x y : Var} : (i ⊨ .forall x a) → i ⊨ (.not $ .exists x (.not a)) := by
  intro h
  have hf : ∀ (v : Val), i[x ↦ v] ⊨ a := Models.forall h
  apply Models.not
  admit
