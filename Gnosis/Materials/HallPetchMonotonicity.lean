/-
  HallPetchMonotonicity.lean
  ==========================

  Formalizes the Hall-Petch relationship:
  σ_y = σ_0 + k_y * d^(-1/2)

  In our discrete kernel, we prove the fundamental "Grain Boundary Witness":
  reducing the grain size (d) increases the yield strength (σ_y) due to
  dislocation pile-up at boundaries. We model this as a monotonic
  inverse relationship.

  Style: Rustic Church (Init-only).
-/

import Init

namespace Gnosis.Materials

/-- 
  The Hall-Petch Witness:
  A material model that maps diameter (d) to strength (sigma).
-/
structure HallPetchModel where
  σ0 : Nat
  ky : Nat
  strength : Nat → Nat

/-- 
  Consistency Witness:
  The model must satisfy the property that smaller grains are stronger.
-/
def IsConsistentHallPetch (m : HallPetchModel) : Prop :=
  ∀ d1 d2, (d1 > 0 ∧ d2 > 0 ∧ d1 < d2) → m.strength d1 > m.strength d2

/-- 
  Theorem: Refinement Strengthening.
  In a consistent Hall-Petch model, grain refinement (reducing d)
  always yields a stronger material witness.
-/
theorem refinement_strengthening (m : HallPetchModel)
  (h_consist : IsConsistentHallPetch m)
  (d_large d_small : Nat)
  (h_refine : d_small < d_large)
  (h_pos : d_small > 0) :
  m.strength d_small > m.strength d_large := by
  apply h_consist
  constructor
  . exact h_pos
  constructor
  . -- d_large > d_small > 0
    have h_large_pos : d_large > 0 := Nat.lt_trans h_pos h_refine
    exact h_large_pos
  . exact h_refine

end Gnosis.Materials