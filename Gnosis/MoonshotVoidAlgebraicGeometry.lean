def VoidLocus (x : Nat) : Prop := x = 0
theorem void_everywhere : ∀ x, VoidLocus (x * 0) := by
  intro x
  rfl