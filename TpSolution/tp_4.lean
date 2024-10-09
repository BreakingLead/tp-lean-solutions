def f (x: Nat) : Nat := x + 1
example (α : Type) (p q: α → Prop)
: (∀ x : α, p x ∧ q x) → ∀ y: α, p y :=
  fun h: ∀ x : α, p x ∧ q x =>
  fun y: α =>
  show p y from (h y).left

#eval (· + 1) <$> [1,2,3,4]
#eval #[1,2,3]
