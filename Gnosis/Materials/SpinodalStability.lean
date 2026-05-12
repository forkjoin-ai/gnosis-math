/-
  SpinodalStability.lean
  ======================

  Formalizes the stability condition for spinodal decomposition.
  Phase separation is spontaneous (unstable) when the second derivative
  of the Gibbs free energy (g) with respect to composition (c) is negative:
  ∂²g/∂c² < 0

  In Gnosis, we model the free energy as a discrete function and the
  second derivative as a central difference.

  Style: Rustic Church (Init-only).
-/

import Init

namespace Gnosis.Materials

/-- 
  Free Energy (g) as a function of discrete composition (c).
-/
def FreeEnergy := Nat → Int

/-- 
  Discrete Second Derivative (Curvature of Energy):
  ∂²g/∂c² ≈ g(c+1) - 2g(c) + g(c-1)
-/
def EnergyCurvature (g : FreeEnergy) (c : Nat) : Int :=
  g (c + 2) - 2 * g (c + 1) + g c

/-- 
  Spinodal Stability Witness:
  A composition c is in the spinodal region (unstable) if the
  energy curvature is negative.
-/
def IsSpinodalUnstable (g : FreeEnergy) (c : Nat) : Prop :=
  EnergyCurvature g c < 0

/-- 
  Theorem: Convex Stability.
  If the free energy is strictly convex (positive curvature), the system
  is stable against spontaneous decomposition.
-/
theorem convex_energy_is_stable (g : FreeEnergy) (c : Nat)
  (h_convex : EnergyCurvature g c > 0) :
  ¬ IsSpinodalUnstable g c := by
  unfold IsSpinodalUnstable
  intro h
  -- h_convex : 0 < EnergyCurvature
  -- h : EnergyCurvature < 0
  have h_not := Int.lt_asymm h_convex h
  exact h_not

end Gnosis.Materials
