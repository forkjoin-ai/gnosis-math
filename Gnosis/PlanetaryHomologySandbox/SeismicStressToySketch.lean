/-!
# Seismic Stress Toy Sketch

Init-only discrete asperity model: load, compare to threshold, and either
retain loaded stress or slip to a residual/subtracted stress.
-/

namespace PlanetaryHomologySandbox

structure AsperityParams where
  critical : Nat
  load : Nat
  residual : Nat
deriving Repr

def stepStress (stress : Nat) (params : AsperityParams) : Nat × Bool :=
  let loaded := stress + params.load
  if params.critical ≤ loaded then
    (params.residual, true)
  else
    (loaded, false)

theorem stepStress_not_rupture_eq
    (stress : Nat)
    (params : AsperityParams)
    (hNoRupture : ¬ (stepStress stress params).2) :
    (stepStress stress params).1 = stress + params.load := by
  by_cases hCritical : params.critical ≤ stress + params.load
  · have hRupture : (stepStress stress params).2 := by
      simp [stepStress, hCritical]
    exact False.elim (hNoRupture hRupture)
  · simp [stepStress, hCritical]

theorem stepStress_rupture_residual
    (stress : Nat)
    (params : AsperityParams)
    (hRupture : (stepStress stress params).2) :
    (stepStress stress params).1 = params.residual := by
  by_cases hCritical : params.critical ≤ stress + params.load
  · simp [stepStress, hCritical]
  · simp [stepStress, hCritical] at hRupture

theorem stepStress_rupture_iff
    (stress : Nat)
    (params : AsperityParams) :
    (stepStress stress params).2 ↔
      params.critical ≤ stress + params.load := by
  by_cases hCritical : params.critical ≤ stress + params.load <;>
    simp [stepStress, hCritical]

structure AsperitySubtractParams where
  critical : Nat
  load : Nat
  drop : Nat
  residual : Nat
deriving Repr

def stepStressSubtract
    (stress : Nat)
    (params : AsperitySubtractParams) : Nat × Bool :=
  let loaded := stress + params.load
  if params.critical ≤ loaded then
    (max params.residual (loaded - params.drop), true)
  else
    (loaded, false)

theorem stepStressSubtract_not_rupture_eq
    (stress : Nat)
    (params : AsperitySubtractParams)
    (hNoRupture : ¬ (stepStressSubtract stress params).2) :
    (stepStressSubtract stress params).1 = stress + params.load := by
  by_cases hCritical : params.critical ≤ stress + params.load
  · have hRupture : (stepStressSubtract stress params).2 := by
      simp [stepStressSubtract, hCritical]
    exact False.elim (hNoRupture hRupture)
  · simp [stepStressSubtract, hCritical]

theorem stepStressSubtract_rupture_max
    (stress : Nat)
    (params : AsperitySubtractParams)
    (hRupture : (stepStressSubtract stress params).2) :
    (stepStressSubtract stress params).1 =
      max params.residual (stress + params.load - params.drop) := by
  by_cases hCritical : params.critical ≤ stress + params.load
  · simp [stepStressSubtract, hCritical]
  · simp [stepStressSubtract, hCritical] at hRupture

theorem stepStressSubtract_rupture_iff
    (stress : Nat)
    (params : AsperitySubtractParams) :
    (stepStressSubtract stress params).2 ↔
      params.critical ≤ stress + params.load := by
  by_cases hCritical : params.critical ≤ stress + params.load <;>
    simp [stepStressSubtract, hCritical]

end PlanetaryHomologySandbox
