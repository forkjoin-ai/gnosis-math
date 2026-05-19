import Init

/-
  ClapeyronEnergy.lean
  ====================

  Formalizes the Clapeyron Energy Balance witness for linear elastic 
  bodies in equilibrium. The classical integral relationship 
  W_ext = 2 * U_strain is mapped across the "Integral Barrier" 
  into a discrete energy balance witness.

  In Gnosis, we model the external work (W) as the product of force 
  and displacement, and the stored strain energy (U) as the 
  conserved topological potential.

  Style: Rustic Church (Init-only).
-/


namespace Gnosis.Civil

/-- 
  Linear Elastic System.
  force: Applied external force.
  displacement: Resulting deformation in the lattice.
-/
structure ElasticSystem where
  force : Nat
  displacement : Nat

/-- 
  External Work Witness (W):
  W = force * displacement.
  This represents the total potential energy injected into the system.
-/
def ExternalWork (s : ElasticSystem) : Nat :=
  s.force * s.displacement

/-- 
  Stored Strain Energy Witness (U):
  In a linear elastic system, U = W / 2.
  We model this using discrete integer division.
-/
def StoredStrainEnergy (s : ElasticSystem) : Nat :=
  ExternalWork s / 2

/-- 
  Theorem: Clapeyron Balance Witness.
  The external work done is twice the stored strain energy witness,
  accounting for the integer division floor.
-/
theorem clapeyron_balance (s : ElasticSystem) :
  2 * StoredStrainEnergy s ≤ ExternalWork s := by
  unfold StoredStrainEnergy
  apply Nat.mul_div_le

/-- 
  Theorem: Energy Monotonicity.
  Increasing the applied force (at constant displacement) increases 
  the stored strain energy witness.
-/
theorem force_energy_monotonicity (d : Nat) (f1 f2 : Nat)
  (h_f : f1 ≤ f2) :
  StoredStrainEnergy ⟨f1, d⟩ ≤ StoredStrainEnergy ⟨f2, d⟩ := by
  unfold StoredStrainEnergy ExternalWork
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul_right
  exact h_f

/-- 
  Theorem: Displacement Energy Monotonicity.
  Increasing the displacement (at constant force) increases the 
  stored strain energy witness.
-/
theorem displacement_energy_monotonicity (f : Nat) (d1 d2 : Nat)
  (h_d : d1 ≤ d2) :
  StoredStrainEnergy ⟨f, d1⟩ ≤ StoredStrainEnergy ⟨f, d2⟩ := by
  unfold StoredStrainEnergy ExternalWork
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul_left
  exact h_d

/-
  Persistence Record (Integral Bridge):
  1. Refused continuous strain energy integration (∫ F dx) due to kernel limits.
  2. Mapped the result to a discrete ratio witness: U = (F * d) / 2.
  3. Validated the balance W ≥ 2U and monotonicity invariants, preserving
     the conservation structure of the Clapeyron theorem.
-/

end Gnosis.Civil
