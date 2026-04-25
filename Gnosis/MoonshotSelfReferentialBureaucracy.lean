def BureaucraticState (α : Type) := α → α

theorem self_referential_bureaucracy {α : Type} (f : BureaucraticState α) (x : α) :
  ∃ y : α, y = f x :=
  ⟨f x, rfl⟩