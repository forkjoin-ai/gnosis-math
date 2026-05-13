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
    rw [if_pos rfl]
    exact Nat.zero_le 100
  | Nat.succ n =>
    rw [if_neg (Nat.succ_ne_zero n)]
    match k with
    | 0 => 
      rw [if_pos rfl]
      exact Nat.zero_le 100
    | Nat.succ m =>
      rw [if_neg (Nat.succ_ne_zero m)]
      let X := Nat.succ m * Nat.succ n
      apply Nat.div_le_of_le_mul
      -- Goal: X * 100 ≤ (1 + X) * 100
      rw [Nat.add_mul, Nat.one_mul]
      apply Nat.le_add_left

end Gnosis.Materials