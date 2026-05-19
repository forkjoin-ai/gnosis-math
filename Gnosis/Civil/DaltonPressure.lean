import Init

/-
  DaltonPressure.lean
  ====================

  Formalizes Dalton's Law of Partial Pressures for discrete gas mixtures.
  The total pressure (P) of a mixture is the sum of the partial pressures
  (p_i) of each component gas.

  In Gnosis, we model this as an "Additive Pressure Witness", proving that
  the total pressure is equal to the sum over all components.

  Style: Rustic Church (Init-only).
-/


namespace Gnosis.Civil

/-- 
  A Gas Mixture.
  partial_pressures: List of partial pressures of each component.
-/
structure GasMixture where
  partial_pressures : List Nat

/-- 
  Total Pressure: Sum of partial pressures.
-/
def total_pressure (m : GasMixture) : Nat :=
  m.partial_pressures.foldl (λ acc p => acc + p) 0

/-- 
  Theorem: Non-negative Total Pressure.
  The total pressure witness is always non-negative.
-/
theorem total_pressure_nonnegative (m : GasMixture) :
  total_pressure m ≥ 0 := by
  apply Nat.zero_le

/-- 
  Theorem: Additive Pressure Witness.
  Adding a component gas increases the total pressure witness.
-/
theorem additive_pressure_witness (ps : List Nat) (p_new : Nat) :
  total_pressure ⟨p_new :: ps⟩ = p_new + total_pressure ⟨ps⟩ := by
  unfold total_pressure
  have h_sum : ∀ (l : List Nat) (a b : Nat), l.foldl (λ x y => x + y) (a + b) = a + l.foldl (λ x y => x + y) b := by
    intro l
    induction l with
    | nil => intro a b; rfl
    | cons x xs ih_xs =>
      intro a b
      show List.foldl (λ x y => x + y) ((a + b) + x) xs = a + List.foldl (λ x y => x + y) (b + x) xs
      rw [Nat.add_assoc]
      apply ih_xs
  rw [List.foldl]
  rw [← Nat.add_zero p_new, Nat.zero_add]
  apply h_sum

end Gnosis.Civil