/-
  YoungLaplace.lean
  =================

  Formalizes the Young-Laplace pressure jump across a curved interface.
  The pressure difference (ΔP) is proportional to the surface tension (γ)
  and the total curvature (κ):
  ΔP = γ * κ

  In Gnosis, we model this as a witness that an interface cannot remain
  curved without a supporting pressure gradient.

  Style: Rustic Church (Init-only).
-/

import Init

namespace Gnosis.Materials

/-- 
  The Pressure Jump Witness (ΔP).
  gamma: Surface Tension
  kappa: Curvature
-/
def PressureJump (gamma : Nat) (kappa : Nat) : Nat :=
  gamma * kappa

/-- 
  Theorem: Flat Interface Witness.
  If the interface is flat (zero curvature), the pressure jump
  must be zero.
-/
theorem flat_interface_zero_jump (gamma : Nat) :
  PressureJump gamma 0 = 0 := by
  unfold PressureJump
  rw [Nat.mul_zero]

/-- 
  Theorem: Curvature Monotonicity.
  Increasing the curvature of an interface (with constant surface tension)
  increases the required pressure jump witness.
-/
theorem curvature_jump_monotonic (gamma : Nat) (k1 k2 : Nat)
  (h_gamma : gamma > 0)
  (h_k : k1 < k2) :
  PressureJump gamma k1 < PressureJump gamma k2 := by
  unfold PressureJump
  apply Nat.mul_lt_mul_of_pos_left
  . exact h_k
  . exact h_gamma

end Gnosis.Materials