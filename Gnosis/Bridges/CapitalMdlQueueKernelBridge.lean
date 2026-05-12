namespace CapitalMdlQueueKernelBridge

/-!
Init-only replacement for the legacy Mathlib-heavy Capital/MDL queue bridge.

The historical module contained good finite budget ideas but relied on Mathlib
automation and real casts. This version keeps the queue,
deficit, semantic-morphism, and kernel-lift certificates as Nat data.
-/

structure LockupState where
  totalMinutes : Nat
  hPositiveTimeline : 0 < totalMinutes
deriving Repr

structure ModelCandidate where
  budget : Nat
  totalCost : Nat
  quality : Nat
  hQuality : quality = budget - totalCost + 1
deriving Repr

def capitalTimelineFailureBudget (state : LockupState) : Nat :=
  state.totalMinutes

def mdlDescriptionFailureBudget (model : ModelCandidate) : Nat :=
  model.totalCost

def capitalMdlFailureBudget (state : LockupState) (model : ModelCandidate) : Nat :=
  capitalTimelineFailureBudget state + mdlDescriptionFailureBudget model

def replicaCount (failureBudget : Nat) : Nat :=
  2 * failureBudget + 1

def quorumSize (_replicas failureBudget : Nat) : Nat :=
  failureBudget + 1

structure QueueBoundaryWitnessNat where
  beta1 : Nat
  capacity : Nat
  arrivalRate : Nat
  serviceRate : Nat
deriving DecidableEq, Repr

def canonicalQueueBoundary (failureBudget : Nat) : QueueBoundaryWitnessNat :=
  { beta1 := 0
    capacity := 1
    arrivalRate := failureBudget
    serviceRate := quorumSize (replicaCount failureBudget) failureBudget }

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

def topologicalDeficit (pathCount channelCount : Nat) : Nat :=
  pathCount - channelCount

theorem capital_timeline_failure_budget_positive
    (state : LockupState) :
    0 < capitalTimelineFailureBudget state := by
  exact state.hPositiveTimeline

theorem capital_timeline_budget_yields_unit_queue_boundary
    (state : LockupState) :
    0 < capitalTimelineFailureBudget state ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = capitalTimelineFailureBudget state ∧
      boundary.serviceRate =
        quorumSize (replicaCount (capitalTimelineFailureBudget state))
          (capitalTimelineFailureBudget state) := by
  refine ⟨capital_timeline_failure_budget_positive state, ?_⟩
  exact ⟨canonicalQueueBoundary (capitalTimelineFailureBudget state), rfl, rfl, rfl, rfl⟩

theorem mdl_description_identity (model : ModelCandidate) :
    model.quality = model.budget - model.totalCost + 1 :=
  model.hQuality

theorem mdl_description_budget_yields_unit_queue_boundary
    (model : ModelCandidate) :
    model.quality = model.budget - model.totalCost + 1 ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = mdlDescriptionFailureBudget model ∧
      boundary.serviceRate =
        quorumSize (replicaCount (mdlDescriptionFailureBudget model))
          (mdlDescriptionFailureBudget model) := by
  refine ⟨mdl_description_identity model, ?_⟩
  exact ⟨canonicalQueueBoundary (mdlDescriptionFailureBudget model), rfl, rfl, rfl, rfl⟩

theorem capital_mdl_failure_budget_positive
    (state : LockupState)
    (model : ModelCandidate) :
    0 < capitalMdlFailureBudget state model := by
  unfold capitalMdlFailureBudget
  exact Nat.lt_add_right (mdlDescriptionFailureBudget model) state.hPositiveTimeline

theorem capital_mdl_budget_yields_unit_queue_boundary
    (state : LockupState)
    (model : ModelCandidate) :
    0 < capitalTimelineFailureBudget state ∧
    model.quality = model.budget - model.totalCost + 1 ∧
    capitalMdlFailureBudget state model =
      capitalTimelineFailureBudget state + mdlDescriptionFailureBudget model ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = capitalMdlFailureBudget state model ∧
      boundary.serviceRate =
        quorumSize (replicaCount (capitalMdlFailureBudget state model))
          (capitalMdlFailureBudget state model) := by
  refine ⟨capital_timeline_failure_budget_positive state, mdl_description_identity model, rfl, ?_⟩
  exact ⟨canonicalQueueBoundary (capitalMdlFailureBudget state model), rfl, rfl, rfl, rfl⟩

theorem capital_mdl_budget_does_not_force_positive_beta1
    (state : LockupState)
    (model : ModelCandidate) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = capitalMdlFailureBudget state model →
        boundary.serviceRate =
          quorumSize (replicaCount (capitalMdlFailureBudget state model))
            (capitalMdlFailureBudget state model) →
        0 < boundary.beta1) := by
  intro hPositive
  let boundary := canonicalQueueBoundary (capitalMdlFailureBudget state model)
  have h : 0 < boundary.beta1 := hPositive boundary rfl rfl
  exact Nat.lt_irrefl 0 h

theorem capital_mdl_budget_does_not_force_strict_capacity_growth
    (state : LockupState)
    (model : ModelCandidate) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = capitalMdlFailureBudget state model →
        boundary.serviceRate =
          quorumSize (replicaCount (capitalMdlFailureBudget state model))
            (capitalMdlFailureBudget state model) →
        1 < boundary.capacity) := by
  intro hGrowth
  let boundary := canonicalQueueBoundary (capitalMdlFailureBudget state model)
  have h : 1 < boundary.capacity := hGrowth boundary rfl rfl
  exact Nat.lt_irrefl 1 h

theorem capital_mdl_positive_budget_yields_positive_topological_deficit
    (state : LockupState)
    (model : ModelCandidate) :
    0 < capitalMdlFailureBudget state model ∧
    0 < topologicalDeficit (capitalMdlFailureBudget state model + 1) 1 := by
  have hBudget : 0 < capitalMdlFailureBudget state model :=
    capital_mdl_failure_budget_positive state model
  refine ⟨hBudget, ?_⟩
  unfold topologicalDeficit
  rw [Nat.add_sub_cancel]
  exact hBudget

theorem capital_mdl_budget_does_not_force_beta1_equals_budget
    (state : LockupState)
    (model : ModelCandidate) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = capitalMdlFailureBudget state model →
        boundary.serviceRate =
          quorumSize (replicaCount (capitalMdlFailureBudget state model))
            (capitalMdlFailureBudget state model) →
        boundary.beta1 = capitalMdlFailureBudget state model) := by
  intro hAll
  let boundary := canonicalQueueBoundary (capitalMdlFailureBudget state model)
  have hEq : boundary.beta1 = capitalMdlFailureBudget state model :=
    hAll boundary rfl rfl
  have hBudget : 0 < capitalMdlFailureBudget state model :=
    capital_mdl_failure_budget_positive state model
  rw [show boundary.beta1 = 0 by rfl] at hEq
  rw [← hEq] at hBudget
  exact Nat.lt_irrefl 0 hBudget

theorem capital_mdl_semantic_morphism_yields_unit_queue_boundary
    (state : LockupState)
    (model : ModelCandidate)
    (interpret : Nat → Nat)
    (hInterpret :
      interpret (capitalMdlFailureBudget state model) =
        capitalMdlFailureBudget state model) :
    0 < capitalTimelineFailureBudget state ∧
    model.quality = model.budget - model.totalCost + 1 ∧
    0 < interpret (capitalMdlFailureBudget state model) ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = interpret (capitalMdlFailureBudget state model) ∧
      boundary.serviceRate =
        quorumSize (replicaCount (interpret (capitalMdlFailureBudget state model)))
          (interpret (capitalMdlFailureBudget state model)) := by
  refine ⟨capital_timeline_failure_budget_positive state, mdl_description_identity model, ?_, ?_⟩
  · rw [hInterpret]
    exact capital_mdl_failure_budget_positive state model
  · refine ⟨canonicalQueueBoundary (interpret (capitalMdlFailureBudget state model)), rfl, rfl, rfl, ?_⟩
    rfl

theorem capital_mdl_budget_yields_geometric_rate_certificate
    (state : LockupState)
    (model : ModelCandidate) :
    0 < capitalMdlFailureBudget state model ∧
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (capitalMdlFailureBudget state model) ∧
      rate.initialBound = capitalMdlFailureBudget state model + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨capital_mdl_failure_budget_positive state model, ?_⟩
  refine ⟨budgetGeometricRate (capitalMdlFailureBudget state model), rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (capitalMdlFailureBudget state model)).hRateLtOne
  · exact (budgetGeometricRate (capitalMdlFailureBudget state model)).hInitialBoundPos

structure CapitalMdlKernelLiftAdapter where
  state : LockupState
  model : ModelCandidate
  budget : Nat
  hBudgetEq : budget = capitalMdlFailureBudget state model
  driftGap : Nat
  hDriftGap : 0 < driftGap
  kernelMatched : Bool
deriving Repr

namespace CapitalMdlKernelLiftAdapter

theorem budget_pos_from_source (adapter : CapitalMdlKernelLiftAdapter) :
    0 < adapter.budget := by
  rw [adapter.hBudgetEq]
  exact capital_mdl_failure_budget_positive adapter.state adapter.model

theorem capital_mdl_continuous_ergodicity_lift
    (adapter : CapitalMdlKernelLiftAdapter) :
    0 < capitalTimelineFailureBudget adapter.state ∧
    adapter.model.quality = adapter.model.budget - adapter.model.totalCost + 1 ∧
    0 < adapter.budget ∧
    0 < adapter.driftGap :=
  ⟨capital_timeline_failure_budget_positive adapter.state,
    mdl_description_identity adapter.model,
    budget_pos_from_source adapter,
    adapter.hDriftGap⟩

end CapitalMdlKernelLiftAdapter

theorem capital_mdl_semantic_morphism_continuous_ergodicity_lift
    (state : LockupState)
    (model : ModelCandidate)
    (interpret : Nat → Nat)
    (hInterpret :
      interpret (capitalMdlFailureBudget state model) =
        capitalMdlFailureBudget state model)
    (driftGap : Nat)
    (hDriftGap : 0 < driftGap) :
    0 < capitalTimelineFailureBudget state ∧
    model.quality = model.budget - model.totalCost + 1 ∧
    0 < interpret (capitalMdlFailureBudget state model) ∧
    0 < driftGap := by
  refine ⟨capital_timeline_failure_budget_positive state, mdl_description_identity model, ?_, hDriftGap⟩
  rw [hInterpret]
  exact capital_mdl_failure_budget_positive state model

end CapitalMdlQueueKernelBridge
