import Init

/-
  ArrheniusBarrier.lean
  =====================

  Formalizes the Arrhenius Activation Barrier witness.
  The classical rate equation k = A exp(-Ea / RT) is mapped across the
  "Transcendental Barrier" into a discrete topological witness.

  In Gnosis, we model the reaction rate (k) as a "Barrier Penetration Witness"
  that is monotonic with respect to the thermal potential (RT) and
  antitonic with respect to the activation energy (Ea).

  Style: Rustic Church (Init-only).
-/


namespace Gnosis.Materials

/-- 
  Arrhenius Parameters.
  ea: Activation Energy (The height of the topological barrier).
  rt: Thermal Potential (The available energy for penetration).
-/
structure ArrheniusParams where
  ea : Nat
  rt : Nat

/-- 
  Reaction Witness (k):
  A discrete measure of barrier penetration. 
  In this model, the witness is the energy surplus available to 
  overcome the barrier: k = rt - ea.
-/
def ReactionWitness (p : ArrheniusParams) : Nat :=
  p.rt - p.ea

/-- 
  Theorem: Barrier Antitonicity.
  Increasing the activation energy (Ea) never increases the 
  reaction witness, reflecting the increased difficulty of 
  barrier penetration.
-/
theorem barrier_antitonicity (rt : Nat) (ea1 ea2 : Nat)
  (h_ea : ea1 ≤ ea2) :
  ReactionWitness ⟨ea2, rt⟩ ≤ ReactionWitness ⟨ea1, rt⟩ := by
  unfold ReactionWitness
  apply Nat.sub_le_sub_left
  exact h_ea

/-- 
  Theorem: Thermal Monotonicity.
  Increasing the thermal potential (RT) never decreases the
  reaction witness, reflecting the increased probability of 
  crossing the activation threshold.
-/
theorem thermal_monotonicity (ea : Nat) (rt1 rt2 : Nat)
  (h_rt : rt1 ≤ rt2) :
  ReactionWitness ⟨ea, rt1⟩ ≤ ReactionWitness ⟨ea, rt2⟩ := by
  unfold ReactionWitness
  apply Nat.sub_le_sub_right
  exact h_rt

/-- 
  Theorem: Threshold Witness.
  If the thermal potential is below the activation energy, the 
  reaction witness saturates to zero.
-/
theorem thermal_threshold_saturation (p : ArrheniusParams)
  (h_below : p.rt ≤ p.ea) :
  ReactionWitness p = 0 := by
  unfold ReactionWitness
  apply Nat.sub_eq_zero_of_le
  exact h_below

/-
  Persistence Record (Transcendental Bridge):
  1. Refused exp(-Ea/RT) due to transcendental kernel limits.
  2. Mapped exponential decay to discrete saturating subtraction (rt - ea).
  3. Preservation of monotonicity/antitonicity invariants ensures 
     topological consistency despite the non-linear compression.
-/

end Gnosis.Materials
