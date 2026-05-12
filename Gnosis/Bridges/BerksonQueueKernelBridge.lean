import Init
import Gnosis.BerksonsParadox

/-!
# Berkson Queue Kernel Bridge

Finite collider-threshold witnesses for Berkson queue MCP rows.
-/

namespace BerksonQueueKernelBridge

def colliderThreshold (cs : BerksonsParadox.ColliderSetup) : Nat :=
  cs.collider_threshold

def totalRejections (cs : BerksonsParadox.ColliderSetup) : Nat :=
  cs.causeA_rejections + cs.causeB_rejections

def replicaCount (budget : Nat) : Nat := 2 * budget + 1

def quorumSize (_replicas budget : Nat) : Nat := budget + 1

structure QueueBoundaryWitnessNat where
  beta1 : Nat
  capacity : Nat
  arrivalRate : Nat
  serviceRate : Nat
deriving DecidableEq, Repr

def canonicalQueueBoundary (budget : Nat) : QueueBoundaryWitnessNat :=
  { beta1 := 0
    capacity := 1
    arrivalRate := budget
    serviceRate := quorumSize (replicaCount budget) budget }

structure GeometricRateNat where
  numerator : Nat
  denominator : Nat
  initialBound : Nat
  hRateLtOne : numerator < denominator
  hDenomPos : 0 < denominator
  hInitialBoundPos : 0 < initialBound
deriving Repr

def budgetGeometricRate (budget : Nat) : GeometricRateNat :=
  { numerator := 3
    denominator := 4
    initialBound := budget + 1
    hRateLtOne := by decide
    hDenomPos := by decide
    hInitialBoundPos := Nat.succ_pos budget }

theorem berkson_selected_implies_threshold_bounded_by_total_rejections
    (cs : BerksonsParadox.ColliderSetup)
    (hSelected : cs.selected) :
    colliderThreshold cs ≤ totalRejections cs := by
  exact hSelected

theorem berkson_selected_collider_yields_unit_queue_boundary
    (cs : BerksonsParadox.ColliderSetup)
    (hSelected : cs.selected) :
    colliderThreshold cs ≤ totalRejections cs ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = colliderThreshold cs ∧
      boundary.serviceRate =
        quorumSize (replicaCount (colliderThreshold cs)) (colliderThreshold cs) := by
  exact ⟨berkson_selected_implies_threshold_bounded_by_total_rejections cs hSelected,
    ⟨canonicalQueueBoundary (colliderThreshold cs), rfl, rfl, rfl, rfl⟩⟩

theorem berkson_selected_collider_does_not_force_positive_beta1
    (cs : BerksonsParadox.ColliderSetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = colliderThreshold cs →
        boundary.serviceRate =
          quorumSize (replicaCount (colliderThreshold cs)) (colliderThreshold cs) →
        0 < boundary.beta1) := by
  intro hAll
  let boundary := canonicalQueueBoundary (colliderThreshold cs)
  exact Nat.lt_irrefl 0 (hAll boundary rfl rfl)

theorem berkson_selected_collider_yields_geometric_rate_certificate
    (cs : BerksonsParadox.ColliderSetup)
    (hSelected : cs.selected) :
    colliderThreshold cs ≤ totalRejections cs ∧
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (colliderThreshold cs) ∧
      rate.initialBound = colliderThreshold cs + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨berkson_selected_implies_threshold_bounded_by_total_rejections cs hSelected, ?_⟩
  refine ⟨budgetGeometricRate (colliderThreshold cs), rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (colliderThreshold cs)).hRateLtOne
  · exact (budgetGeometricRate (colliderThreshold cs)).hInitialBoundPos

structure BerksonKernelLiftBundle where
  collider : BerksonsParadox.ColliderSetup
  hSelected : collider.selected
  budget : Nat
  hBudgetEq : budget = colliderThreshold collider
  driftGap : Nat
  hDriftGap : 0 < driftGap

end BerksonQueueKernelBridge

namespace BerksonKernelLiftAdapter

abbrev BerksonKernelLiftBundle :=
  BerksonQueueKernelBridge.BerksonKernelLiftBundle

theorem selected_continuous_ergodicity_lift
    (adapter : BerksonKernelLiftBundle) :
    BerksonQueueKernelBridge.colliderThreshold adapter.collider ≤
      BerksonQueueKernelBridge.totalRejections adapter.collider ∧
    adapter.budget = BerksonQueueKernelBridge.colliderThreshold adapter.collider ∧
    0 < adapter.driftGap :=
  ⟨BerksonQueueKernelBridge.berkson_selected_implies_threshold_bounded_by_total_rejections
      adapter.collider
      adapter.hSelected,
    adapter.hBudgetEq,
    adapter.hDriftGap⟩

end BerksonKernelLiftAdapter
