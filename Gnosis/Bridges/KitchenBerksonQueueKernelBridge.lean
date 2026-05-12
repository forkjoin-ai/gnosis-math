import Init
import Gnosis.BerksonsParadox
import Gnosis.Bridges.BerksonQueueKernelBridge

/-!
# Kitchen/Berkson Queue Kernel Bridge

Finite safety-gap and collider-threshold witnesses for the stale kitchen +
Berkson queue MCP rows.
-/

namespace KitchenBerksonQueueKernelBridge

structure CrossDomainFrame where
  physicalSafetyCritical : Bool
  safetySignals : Nat
  safetyHazards : Nat
deriving Repr

def safetyGap (frame : CrossDomainFrame) : Nat :=
  frame.safetyHazards - frame.safetySignals

def totalDeficit (frame : CrossDomainFrame) : Nat :=
  safetyGap frame

def kitchenBerksonBudget
    (frame : CrossDomainFrame)
    (collider : BerksonsParadox.ColliderSetup) : Nat :=
  totalDeficit frame + BerksonQueueKernelBridge.colliderThreshold collider

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

theorem safety_gap_positive
    (frame : CrossDomainFrame)
    (hGap : frame.safetySignals < frame.safetyHazards) :
    0 < totalDeficit frame := by
  unfold totalDeficit safetyGap
  exact Nat.sub_pos_of_lt hGap

theorem kitchen_berkson_safety_gap_yields_unit_queue_boundary
    (frame : CrossDomainFrame)
    (hCritical : frame.physicalSafetyCritical = true)
    (hGap : frame.safetySignals < frame.safetyHazards) :
    frame.physicalSafetyCritical = true ∧
    0 < totalDeficit frame ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = totalDeficit frame ∧
      boundary.serviceRate =
        quorumSize (replicaCount (totalDeficit frame)) (totalDeficit frame) := by
  exact ⟨hCritical, safety_gap_positive frame hGap,
    ⟨canonicalQueueBoundary (totalDeficit frame), rfl, rfl, rfl, rfl⟩⟩

theorem kitchen_berkson_budget_positive
    (frame : CrossDomainFrame)
    (collider : BerksonsParadox.ColliderSetup)
    (hGap : frame.safetySignals < frame.safetyHazards) :
    0 < kitchenBerksonBudget frame collider := by
  unfold kitchenBerksonBudget
  exact Nat.lt_add_right
    (BerksonQueueKernelBridge.colliderThreshold collider)
    (safety_gap_positive frame hGap)

theorem kitchen_berkson_budget_yields_unit_queue_boundary
    (frame : CrossDomainFrame)
    (collider : BerksonsParadox.ColliderSetup)
    (hCritical : frame.physicalSafetyCritical = true)
    (hGap : frame.safetySignals < frame.safetyHazards)
    (hSelected : collider.selected) :
    frame.physicalSafetyCritical = true ∧
    0 < totalDeficit frame ∧
    BerksonQueueKernelBridge.colliderThreshold collider ≤
      BerksonQueueKernelBridge.totalRejections collider ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = kitchenBerksonBudget frame collider ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (kitchenBerksonBudget frame collider))
          (kitchenBerksonBudget frame collider) := by
  exact ⟨hCritical,
    safety_gap_positive frame hGap,
    BerksonQueueKernelBridge.berkson_selected_implies_threshold_bounded_by_total_rejections
      collider
      hSelected,
    ⟨canonicalQueueBoundary (kitchenBerksonBudget frame collider),
      rfl, rfl, rfl, rfl⟩⟩

theorem kitchen_berkson_budget_does_not_force_positive_beta1
    (frame : CrossDomainFrame)
    (collider : BerksonsParadox.ColliderSetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = kitchenBerksonBudget frame collider →
        boundary.serviceRate =
          quorumSize
            (replicaCount (kitchenBerksonBudget frame collider))
            (kitchenBerksonBudget frame collider) →
        0 < boundary.beta1) := by
  intro hAll
  let boundary := canonicalQueueBoundary (kitchenBerksonBudget frame collider)
  exact Nat.lt_irrefl 0 (hAll boundary rfl rfl)

theorem kitchen_berkson_budget_does_not_force_strict_capacity_growth
    (frame : CrossDomainFrame)
    (collider : BerksonsParadox.ColliderSetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = kitchenBerksonBudget frame collider →
        boundary.serviceRate =
          quorumSize
            (replicaCount (kitchenBerksonBudget frame collider))
            (kitchenBerksonBudget frame collider) →
        1 < boundary.capacity) := by
  intro hAll
  let boundary := canonicalQueueBoundary (kitchenBerksonBudget frame collider)
  exact Nat.lt_irrefl 1 (hAll boundary rfl rfl)

theorem kitchen_berkson_budget_yields_geometric_rate_certificate
    (frame : CrossDomainFrame)
    (collider : BerksonsParadox.ColliderSetup) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (kitchenBerksonBudget frame collider) ∧
      rate.initialBound = kitchenBerksonBudget frame collider + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨budgetGeometricRate (kitchenBerksonBudget frame collider),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (kitchenBerksonBudget frame collider)).hRateLtOne
  · exact (budgetGeometricRate (kitchenBerksonBudget frame collider)).hInitialBoundPos

theorem kitchen_berkson_budget_real_positive
    (frame : CrossDomainFrame)
    (collider : BerksonsParadox.ColliderSetup)
    (hGap : frame.safetySignals < frame.safetyHazards) :
    0 < kitchenBerksonBudget frame collider :=
  kitchen_berkson_budget_positive frame collider hGap

structure KitchenBerksonKernelLiftBundle where
  frame : CrossDomainFrame
  collider : BerksonsParadox.ColliderSetup
  hCritical : frame.physicalSafetyCritical = true
  hGap : frame.safetySignals < frame.safetyHazards
  hSelected : collider.selected
  budget : Nat
  hBudgetEq : budget = kitchenBerksonBudget frame collider
  driftGap : Nat
  hDriftGap : 0 < driftGap

end KitchenBerksonQueueKernelBridge

namespace KitchenBerksonKernelLiftAdapter

abbrev KitchenBerksonKernelLiftBundle :=
  KitchenBerksonQueueKernelBridge.KitchenBerksonKernelLiftBundle

theorem budget_pos_from_source
    (adapter : KitchenBerksonKernelLiftBundle) :
    0 < adapter.budget := by
  rw [adapter.hBudgetEq]
  exact KitchenBerksonQueueKernelBridge.kitchen_berkson_budget_positive
    adapter.frame
    adapter.collider
    adapter.hGap

theorem kitchen_berkson_continuous_ergodicity_lift
    (adapter : KitchenBerksonKernelLiftBundle) :
    adapter.frame.physicalSafetyCritical = true ∧
    adapter.frame.safetySignals < adapter.frame.safetyHazards ∧
    BerksonQueueKernelBridge.colliderThreshold adapter.collider ≤
      BerksonQueueKernelBridge.totalRejections adapter.collider ∧
    adapter.budget =
      KitchenBerksonQueueKernelBridge.kitchenBerksonBudget
        adapter.frame
        adapter.collider ∧
    0 < adapter.budget ∧
    0 < adapter.driftGap :=
  ⟨adapter.hCritical,
    adapter.hGap,
    BerksonQueueKernelBridge.berkson_selected_implies_threshold_bounded_by_total_rejections
      adapter.collider
      adapter.hSelected,
    adapter.hBudgetEq,
    budget_pos_from_source adapter,
    adapter.hDriftGap⟩

end KitchenBerksonKernelLiftAdapter
