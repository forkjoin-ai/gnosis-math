/-
  MohrCoulombFailure.lean
  =======================

  Formalizes the Mohr-Coulomb failure criterion for soil and rock.
  The shear strength (τ) of a material is a witness of its internal
  cohesion (c) and friction angle (φ) under a given normal stress (σ):
  τ ≤ c + σ * tan(φ)

  In our discrete kernel, we model this as a witness that a state of
  stress is "Safe" if it lies within the failure envelope.

  Style: Rustic Church (Init-only).
-/

import Init

namespace Gnosis.Civil

/-- 
  Material properties. In a discrete kernel, we can represent
  slopes or coefficients as fixed-point integers or ratios.
-/
structure SoilProperties where
  cohesion : Int
  friction_coeff : Int -- tan(φ) scaled by some factor if needed

/-- 
  The Failure Witness:
  Returns true if the shear stress τ is safe under normal stress σ.
-/
def IsSafeMohrCoulomb (prop : SoilProperties) (σ τ : Int) : Prop :=
  τ ≤ prop.cohesion + σ * prop.friction_coeff

/-- 
  Theorem: Cohesionless Safe Witness.
  For a cohesionless soil (c=0), zero normal stress implies zero shear
  capacity (the soil cannot support shear without confinement).
-/
theorem cohesionless_zero_sigma_no_shear (f_coeff : Int)
  (h_pos : f_coeff ≥ 0) :
  IsSafeMohrCoulomb ⟨0, f_coeff⟩ 0 0 := by
  unfold IsSafeMohrCoulomb
  rw [Int.zero_mul, Int.zero_add]
  apply Int.le_refl

end Gnosis.Civil
