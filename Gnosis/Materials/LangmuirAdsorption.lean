/-
  LangmuirAdsorption.lean
  =======================

  Formalizes the Langmuir Adsorption Isotherm for monolayer coverage.
  The fraction of occupied surface sites (θ) is related to pressure (P)
  and the adsorption constant (K):
  θ = KP / (1 + KP)

  In Gnosis, we model this as a witness of surface occupancy saturation.
  As pressure (P) increases, the coverage θ approaches a limit.

  Style: Rustic Church (Init-only).
-/

import Init

namespace Gnosis.Materials

/-- 
  Simplified Discrete Langmuir Model:
  As pressure (P) increases, coverage increases monotonically.
-/
def LangmuirCoverage (p : Nat) (k : Nat) : Nat :=
  if p = 0 then 0
  else if k = 0 then 0
  else (k * p * 100) / (1 + k * p)

/-- 
  Theorem: Zero Pressure Adsorption.
  At zero pressure, the surface coverage witness must be zero.
-/
theorem zero_pressure_no_adsorption (k : Nat) :
  LangmuirCoverage 0 k = 0 := by
  unfold LangmuirCoverage
  rw [if_pos rfl]

/-- 
  Theorem: Saturation Limit Witness.
  The coverage is always bounded by 100% (saturation).
-/
theorem adsorption_saturation_limit (p k : Nat) :
  LangmuirCoverage p k ≤ 100 := by
  unfold LangmuirCoverage
  match p with
  | 0 => 
    show (if 0 = 0 then 0 else if k = 0 then 0 else k * 0 * 100 / (1 + k * 0)) ≤ 100
    rw [if_pos rfl]
    exact Nat.zero_le 100
  | Nat.succ n =>
    match k with
    | 0 => 
      show (if n.succ = 0 then 0 else if 0 = 0 then 0 else 0 * n.succ * 100 / (1 + 0 * n.succ)) ≤ 100
      rw [if_neg (Nat.succ_ne_zero n), if_pos rfl]
      exact Nat.zero_le 100
    | Nat.succ m =>
      show (if n.succ = 0 then 0 else if m.succ = 0 then 0 else m.succ * n.succ * 100 / (1 + m.succ * n.succ)) ≤ 100
      rw [if_neg (Nat.succ_ne_zero n), if_neg (Nat.succ_ne_zero m)]
      set X := m.succ * n.succ
      apply Nat.div_le_of_le_mul
      -- X * 100 ≤ 100 * (1 + X)
      rw [Nat.mul_add, Nat.mul_one]
      apply Nat.le_add_left

end Gnosis.Materials
