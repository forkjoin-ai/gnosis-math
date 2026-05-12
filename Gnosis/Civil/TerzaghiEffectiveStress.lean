/-
  TerzaghiEffectiveStress.lean
  ============================

  Formalizes Terzaghi's Principle of Effective Stress for saturated porous
  media. The total stress (σ) is decomposed into the effective stress (σ')
  and the pore water pressure (u):
  σ = σ' + u

  In our discrete Gnosis kernel, this is treated as a conservation law
  witness. Stability in soil mechanics is determined by the effective
  stress, which represents the inter-granular forces.

  Style: Rustic Church (Init-only).
-/

import Init

namespace Gnosis.Civil

/-- 
  The Effective Stress Witness:
  Given total stress and pore pressure, calculates the stress carried
  by the soil skeleton.
-/
def effective_stress (total_σ : Int) (u : Int) : Int :=
  total_σ - u

/-- 
  Theorem: Effective Stress Decomposition.
  Total stress is exactly the sum of effective stress and pore pressure.
-/
theorem terzaghi_decomposition (σ σ_prime u : Int)
  (h : σ_prime = effective_stress σ u) :
  σ = σ_prime + u := by
  rw [h]
  unfold effective_stress
  -- σ - u + u = σ
  rw [Int.sub_add_cancel]

/-- 
  Theorem: Zero Pore Pressure Identity.
  If pore pressure is zero, total stress equals effective stress.
-/
theorem zero_pore_pressure_identity (σ : Int) :
  σ = effective_stress σ 0 := by
  unfold effective_stress
  rw [Int.sub_zero]

end Gnosis.Civil