/-
  MonodKinetics.lean
  ==================

  Formalizes the Monod equation for microbial growth in biochemical
  engineering. The specific growth rate (μ) is related to the substrate
  concentration (S) and the half-saturation constant (Ks):
  μ = μ_max * S / (Ks + S)

  In Gnosis, we model this as a "Substrate Saturation Witness", proving
  that the growth rate is bounded by μ_max.

  Style: Rustic Church (Init-only).
-/

import Init

namespace Gnosis.Civil

/-- 
  Monod Parameters.
  mu_max: Maximum specific growth rate.
  ks: Half-velocity constant.
-/
structure MonodParameters where
  mu_max : Nat
  ks : Nat

/-- 
  Monod Growth Rate Witness:
  μ = (mu_max * s) / (ks + s)
-/
def MonodGrowthRate (m : MonodParameters) (s : Nat) : Nat :=
  if s = 0 then 0
  else (m.mu_max * s) / (m.ks + s)

/-- 
  Theorem: Growth Rate Boundary.
  The specific growth rate witness is always bounded by mu_max.
-/
theorem growth_rate_bounded (m : MonodParameters) (s : Nat) :
  MonodGrowthRate m s ≤ m.mu_max := by
  unfold MonodGrowthRate
  match s with
  | 0 => 
    rw [if_pos rfl]
    exact Nat.zero_le m.mu_max
  | Nat.succ n =>
    rw [if_neg (Nat.succ_ne_zero n)]
    apply Nat.div_le_of_le_mul
    -- Goal: mu_max * n.succ ≤ (ks + n.succ) * mu_max
    rw [Nat.mul_comm (m.ks + n.succ)]
    rw [Nat.mul_add]
    apply Nat.le_add_left

end Gnosis.Civil
