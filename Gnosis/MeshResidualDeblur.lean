import Gnosis.BoundedFluidResidual
import Gnosis.PleromaticResidualAtlas

/-!
# Gnosis.MeshResidualDeblur — Topology-Gated Residual Lift

This module formalizes the residual deblur admission gate. It proves that a
topology-gated residual lift (with overpotential and saturation limits)
is structurally bounded, aligning with the Pleromatic mesh's fluid residual constraints.

## The Mesh Residual Primitives
1. `AdmissionGate`: The topology and depth confidence threshold.
2. `Overpotential`: The eta multiplier for the residual lift.
3. `SaturationLimit`: The maximum allowable per-channel delta.
-/

namespace Gnosis
namespace MeshResidualDeblur

/-- The gate is bounded between 0 and 1. -/
def is_valid_gate (gate : Int) : Prop :=
  0 ≤ gate ∧ gate ≤ 1

/-- The saturation limit bounds the maximum residual lift. -/
def bounded_lift (residual : Int) (gate : Int) (eta : Int) (sat : Int) (lift : Int) : Prop :=
  lift = min (max (eta * gate * residual) (-sat)) sat

/-- 
Theorem: Mesh-Gated Residual Bound.
The topology-gated residual lift is strictly bounded by the saturation limit,
ensuring that the mesh does not over-amplify noise in the void.
-/
theorem mesh_gated_residual_bound
    (residual : Int) (gate : Int) (eta : Int) (sat : Int) (lift : Int)
    (h_sat : 0 ≤ sat)
    (h_lift : bounded_lift residual gate eta sat lift) :
    -sat ≤ lift ∧ lift ≤ sat := by
  unfold bounded_lift at h_lift
  rw [h_lift]
  constructor
  · have h1 : -sat ≤ max (eta * gate * residual) (-sat) := by
      exact Int.le_max_right _ _
    have h2 : -sat ≤ 0 := Int.neg_nonpos_of_nonneg h_sat
    have h3 : -sat ≤ sat := Int.le_trans h2 h_sat
    exact Int.le_min.mpr ⟨h1, h3⟩
  · exact Int.min_le_right _ _

/-- 
Theorem: Flat Field Inertia.
If the residual is 0 (the field is flat and structureless), the applied lift is 0.
-/
theorem flat_field_inertia
    (gate : Int) (eta : Int) (sat : Int) (lift : Int)
    (h_sat : 0 ≤ sat)
    (h_lift : bounded_lift 0 gate eta sat lift) :
    lift = 0 := by
  unfold bounded_lift at h_lift
  rw [h_lift]
  have h1 : eta * gate * 0 = 0 := by rw [Int.mul_zero]
  rw [h1]
  have h2 : max 0 (-sat) = 0 := by
    apply Int.max_eq_left
    exact Int.neg_nonpos_of_nonneg h_sat
  rw [h2]
  apply Int.min_eq_left
  exact h_sat

end MeshResidualDeblur
end Gnosis
