/-
  MonodKinetics.lean
  ==================

  Formalizes Monod Kinetics for microorganism growth.
  The specific growth rate (μ) is related to the substrate concentration (S):
  μ = μ_max * S / (K_s + S)

  In Gnosis, we model this as a "Saturating Growth Witness". As substrate
  concentration increases, growth rate increases but is bounded by
  the maximum capacity.

  Style: Rustic Church (Init-only).
-/

import Init

namespace Gnosis.Civil

/-- 
  Growth Rate Model Parameters.
-/
structure MonodModel where
  mu_max : Nat
  ks : Nat

/-- 
  The Growth Rate Witness (μ):
  Calculates growth rate for a given substrate concentration S.
-/
def growth_rate (m : MonodModel) (s : Nat) : Nat :=
  if s = 0 then 0
  else (m.mu_max * s) / (m.ks + s)

/-- 
  Theorem: Zero Substrate No Growth.
  If the substrate concentration is zero, the growth rate witness is zero.
-/
theorem zero_substrate_zero_growth (m : MonodModel) :
  growth_rate m 0 = 0 := rfl

/-- 
  Theorem: Growth Capacity Witness.
  The growth rate is always bounded by the maximum growth rate (μ_max).
-/
theorem growth_rate_bounded (m : MonodModel) (s : Nat) :
  growth_rate m s ≤ m.mu_max := by
  unfold growth_rate
  match s with
  | 0 => exact Nat.zero_le _
  | Nat.succ n =>
    rw [if_neg (Nat.succ_ne_zero n)]
    -- (mu_max * S) / (ks + S) ≤ mu_max
    apply Nat.div_le_of_le_mul
    -- mu_max * S ≤ mu_max * (ks + S)
    have h : m.mu_max * Nat.succ n ≤ (m.ks + Nat.succ n) * m.mu_max := by
      rw [Nat.add_mul, Nat.mul_comm]
      apply Nat.le_add_left
    exact h

end Gnosis.Civil