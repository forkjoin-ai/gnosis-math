import Init
import Gnosis.GeometricErgodicity

/-!
# Baryogenesis/Bureaucracy Queue Kernel Bridge

Paths-lost baryogenesis accounting and bureaucracy stabilization routed through
strict-majority queue witnesses, geometric-rate certificates, and an explicit
continuous-ergodicity lift adapter.
-/

namespace BaryogenesisBureaucracyQueueKernelBridge

structure BaryonViolationWitness where
  pathsBefore : Nat
  pathsAfter : Nat
  hLost : pathsAfter < pathsBefore
deriving Repr

structure BureaucraticFilter where
  bureaucraticDepth : Nat
  governanceOscillation : Nat
  stabilizationFactor : Nat
  hDepth : 0 < bureaucraticDepth
  hStabilizes : governanceOscillation < stabilizationFactor
deriving Repr

def baryogenesisErasureBudget (baryon : BaryonViolationWitness) : Nat :=
  baryon.pathsBefore - baryon.pathsAfter

def bureaucracyStabilizationBudget (_filter : BureaucraticFilter) : Nat := 1

def combinedFailureBudget
    (baryon : BaryonViolationWitness)
    (filter : BureaucraticFilter) : Nat :=
  baryogenesisErasureBudget baryon + bureaucracyStabilizationBudget filter

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

theorem baryogenesis_erasure_budget_positive
    (baryon : BaryonViolationWitness) :
    0 < baryogenesisErasureBudget baryon := by
  unfold baryogenesisErasureBudget
  exact Nat.sub_pos_of_lt baryon.hLost

theorem combined_failure_budget_positive
    (baryon : BaryonViolationWitness)
    (filter : BureaucraticFilter) :
    0 < combinedFailureBudget baryon filter := by
  unfold combinedFailureBudget
  exact Nat.lt_add_right
    (bureaucracyStabilizationBudget filter)
    (baryogenesis_erasure_budget_positive baryon)

theorem baryogenesis_erasure_yields_unit_queue_boundary
    (baryon : BaryonViolationWitness) :
    0 < baryogenesisErasureBudget baryon ∧
    2 * baryogenesisErasureBudget baryon <
      replicaCount (baryogenesisErasureBudget baryon) ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = baryogenesisErasureBudget baryon ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (baryogenesisErasureBudget baryon))
          (baryogenesisErasureBudget baryon) := by
  exact
    ⟨baryogenesis_erasure_budget_positive baryon,
      Nat.lt_succ_self (2 * baryogenesisErasureBudget baryon),
      ⟨canonicalQueueBoundary (baryogenesisErasureBudget baryon),
        rfl, rfl, rfl, rfl⟩⟩

theorem bureaucracy_stabilization_yields_unit_queue_boundary
    (filter : BureaucraticFilter) :
    0 < filter.bureaucraticDepth ∧
    filter.governanceOscillation < filter.stabilizationFactor ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = bureaucracyStabilizationBudget filter ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (bureaucracyStabilizationBudget filter))
          (bureaucracyStabilizationBudget filter) := by
  exact
    ⟨filter.hDepth,
      filter.hStabilizes,
      ⟨canonicalQueueBoundary (bureaucracyStabilizationBudget filter),
        rfl, rfl, rfl, rfl⟩⟩

theorem baryogenesis_bureaucracy_budget_yields_unit_queue_boundary
    (baryon : BaryonViolationWitness)
    (filter : BureaucraticFilter) :
    0 < combinedFailureBudget baryon filter ∧
    2 * combinedFailureBudget baryon filter <
      replicaCount (combinedFailureBudget baryon filter) ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = combinedFailureBudget baryon filter ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (combinedFailureBudget baryon filter))
          (combinedFailureBudget baryon filter) := by
  exact
    ⟨combined_failure_budget_positive baryon filter,
      Nat.lt_succ_self (2 * combinedFailureBudget baryon filter),
      ⟨canonicalQueueBoundary (combinedFailureBudget baryon filter),
        rfl, rfl, rfl, rfl⟩⟩

theorem baryogenesis_bureaucracy_budget_does_not_force_beta1_equals_budget
    (baryon : BaryonViolationWitness)
    (filter : BureaucraticFilter) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = combinedFailureBudget baryon filter →
        boundary.serviceRate =
          quorumSize
            (replicaCount (combinedFailureBudget baryon filter))
            (combinedFailureBudget baryon filter) →
        boundary.beta1 = combinedFailureBudget baryon filter) := by
  intro hAll
  let boundary := canonicalQueueBoundary (combinedFailureBudget baryon filter)
  have hEq : boundary.beta1 = combinedFailureBudget baryon filter :=
    hAll boundary rfl rfl
  have hPositive : 0 < combinedFailureBudget baryon filter :=
    combined_failure_budget_positive baryon filter
  rw [show boundary.beta1 = 0 by rfl] at hEq
  rw [← hEq] at hPositive
  exact Nat.lt_irrefl 0 hPositive

theorem baryogenesis_bureaucracy_budget_yields_geometric_rate_certificate
    (baryon : BaryonViolationWitness)
    (filter : BureaucraticFilter) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (combinedFailureBudget baryon filter) ∧
      rate.initialBound = combinedFailureBudget baryon filter + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine
    ⟨budgetGeometricRate (combinedFailureBudget baryon filter),
      rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (combinedFailureBudget baryon filter)).hRateLtOne
  · exact (budgetGeometricRate (combinedFailureBudget baryon filter)).hInitialBoundPos

structure BaryogenesisBureaucracyKernelLiftBundle (Ω : Type) (maxQueue : Nat) where
  baryon : BaryonViolationWitness
  filter : BureaucraticFilter
  embedding : Gnosis.DiscreteSubLatticeEmbedding Ω maxQueue
  witness : Gnosis.GeometricErgodicWitness maxQueue
  hKernelMatch : witness.envelope.kernel = embedding.discreteKernel
  driftBudget : Nat
  hDriftBudget :
    driftBudget = combinedFailureBudget baryon filter

end BaryogenesisBureaucracyQueueKernelBridge

namespace BaryogenesisBureaucracyKernelLiftAdapter

abbrev BaryonViolationWitness :=
  BaryogenesisBureaucracyQueueKernelBridge.BaryonViolationWitness
abbrev BureaucraticFilter :=
  BaryogenesisBureaucracyQueueKernelBridge.BureaucraticFilter
abbrev BaryogenesisBureaucracyKernelLiftBundle :=
  BaryogenesisBureaucracyQueueKernelBridge.BaryogenesisBureaucracyKernelLiftBundle

theorem baryogenesis_bureaucracy_continuous_ergodicity_lift
    {Ω : Type}
    {maxQueue : Nat}
    (adapter : BaryogenesisBureaucracyKernelLiftBundle Ω maxQueue) :
    0 < BaryogenesisBureaucracyQueueKernelBridge.combinedFailureBudget
      adapter.baryon
      adapter.filter ∧
    adapter.driftBudget =
      BaryogenesisBureaucracyQueueKernelBridge.combinedFailureBudget
        adapter.baryon
        adapter.filter ∧
    adapter.embedding.continuousKernel.fosterDrift ∧
    0 < adapter.embedding.continuousKernel.driftGap ∧
    adapter.witness.rate.rateNumerator < adapter.witness.rate.rateDenominator := by
  have hLift :=
    Gnosis.continuous_ergodicity_lift
      adapter.embedding
      adapter.witness
      adapter.hKernelMatch
  exact
    ⟨BaryogenesisBureaucracyQueueKernelBridge.combined_failure_budget_positive
        adapter.baryon
        adapter.filter,
      adapter.hDriftBudget,
      hLift.1,
      hLift.2.1,
      hLift.2.2⟩

end BaryogenesisBureaucracyKernelLiftAdapter
