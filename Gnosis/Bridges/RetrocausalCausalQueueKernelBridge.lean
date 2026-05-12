import Init

/-!
# Retrocausal/Causal Queue Kernel Bridge

Finite trajectory-budget witnesses for the old retrocausal + causal-adjustment
MCP bridge.
-/

namespace RetrocausalCausalQueueKernelBridge

structure RetrocausalWitness where
  trajectory : List Nat
  hNonempty : trajectory ≠ []
deriving Repr

structure CausalAdjustmentBudget where
  R : Nat
  treat : Nat
  confound : Nat
  hBound : treat + confound ≤ R
deriving Repr

def trajectoryBudget (witness : RetrocausalWitness) : Nat :=
  witness.trajectory.length

def causalAdjustmentBudget (adjustment : CausalAdjustmentBudget) : Nat :=
  adjustment.treat + adjustment.confound

def causalGodWeight (adjustment : CausalAdjustmentBudget) : Nat :=
  adjustment.R - causalAdjustmentBudget adjustment + 1

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

theorem retrocausal_nonempty_budget_positive
    (witness : RetrocausalWitness) :
    0 < trajectoryBudget witness := by
  unfold trajectoryBudget
  cases hTrajectory : witness.trajectory with
  | nil =>
      exact False.elim (witness.hNonempty hTrajectory)
  | cons _ _ =>
      exact Nat.succ_pos _

theorem causal_adjustment_conservation
    (adjustment : CausalAdjustmentBudget) :
    causalGodWeight adjustment + causalAdjustmentBudget adjustment =
      adjustment.R + 1 := by
  unfold causalGodWeight causalAdjustmentBudget
  rw [Nat.add_assoc, Nat.add_comm 1 (adjustment.treat + adjustment.confound), ← Nat.add_assoc]
  rw [Nat.sub_add_cancel adjustment.hBound]

theorem retrocausal_nonempty_trajectory_yields_unit_queue_boundary
    (witness : RetrocausalWitness) :
    0 < trajectoryBudget witness ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = trajectoryBudget witness ∧
      boundary.serviceRate =
        quorumSize (replicaCount (trajectoryBudget witness)) (trajectoryBudget witness) := by
  exact ⟨retrocausal_nonempty_budget_positive witness,
    ⟨canonicalQueueBoundary (trajectoryBudget witness), rfl, rfl, rfl, rfl⟩⟩

theorem retrocausal_causal_budget_bridge_yields_unit_queue_boundary
    (witness : RetrocausalWitness)
    (adjustment : CausalAdjustmentBudget)
    (hBridge : trajectoryBudget witness = causalAdjustmentBudget adjustment) :
    causalGodWeight adjustment + causalAdjustmentBudget adjustment =
      adjustment.R + 1 ∧
    trajectoryBudget witness = causalAdjustmentBudget adjustment ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = trajectoryBudget witness ∧
      boundary.serviceRate =
        quorumSize (replicaCount (trajectoryBudget witness)) (trajectoryBudget witness) := by
  exact ⟨causal_adjustment_conservation adjustment, hBridge,
    ⟨canonicalQueueBoundary (trajectoryBudget witness), rfl, rfl, rfl, rfl⟩⟩

theorem retrocausal_budget_does_not_force_positive_beta1
    (witness : RetrocausalWitness) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = trajectoryBudget witness →
        boundary.serviceRate =
          quorumSize (replicaCount (trajectoryBudget witness)) (trajectoryBudget witness) →
        0 < boundary.beta1) := by
  intro hAll
  let boundary := canonicalQueueBoundary (trajectoryBudget witness)
  exact Nat.lt_irrefl 0 (hAll boundary rfl rfl)

theorem retrocausal_budget_does_not_force_strict_capacity_growth
    (witness : RetrocausalWitness) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = trajectoryBudget witness →
        boundary.serviceRate =
          quorumSize (replicaCount (trajectoryBudget witness)) (trajectoryBudget witness) →
        1 < boundary.capacity) := by
  intro hAll
  let boundary := canonicalQueueBoundary (trajectoryBudget witness)
  exact Nat.lt_irrefl 1 (hAll boundary rfl rfl)

theorem retrocausal_nonempty_yields_geometric_rate_certificate
    (witness : RetrocausalWitness) :
    0 < trajectoryBudget witness ∧
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (trajectoryBudget witness) ∧
      rate.initialBound = trajectoryBudget witness + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨retrocausal_nonempty_budget_positive witness, ?_⟩
  refine ⟨budgetGeometricRate (trajectoryBudget witness),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (trajectoryBudget witness)).hRateLtOne
  · exact (budgetGeometricRate (trajectoryBudget witness)).hInitialBoundPos

structure RetrocausalCausalKernelLiftBundle where
  witness : RetrocausalWitness
  adjustment : CausalAdjustmentBudget
  hBridge : trajectoryBudget witness = causalAdjustmentBudget adjustment
  budget : Nat
  hBudgetEq : budget = trajectoryBudget witness
  driftGap : Nat
  hDriftGap : 0 < driftGap
deriving Repr

end RetrocausalCausalQueueKernelBridge

namespace RetrocausalCausalKernelLiftAdapter

abbrev RetrocausalCausalKernelLiftBundle :=
  RetrocausalCausalQueueKernelBridge.RetrocausalCausalKernelLiftBundle

theorem budget_pos_from_source
    (adapter : RetrocausalCausalKernelLiftBundle) :
    0 < adapter.budget := by
  rw [adapter.hBudgetEq]
  exact RetrocausalCausalQueueKernelBridge.retrocausal_nonempty_budget_positive adapter.witness

theorem retrocausal_causal_continuous_ergodicity_lift
    (adapter : RetrocausalCausalKernelLiftBundle) :
    adapter.budget =
      RetrocausalCausalQueueKernelBridge.trajectoryBudget adapter.witness ∧
    RetrocausalCausalQueueKernelBridge.trajectoryBudget adapter.witness =
      RetrocausalCausalQueueKernelBridge.causalAdjustmentBudget adapter.adjustment ∧
    0 < adapter.budget ∧
    0 < adapter.driftGap :=
  ⟨adapter.hBudgetEq, adapter.hBridge, budget_pos_from_source adapter, adapter.hDriftGap⟩

end RetrocausalCausalKernelLiftAdapter
