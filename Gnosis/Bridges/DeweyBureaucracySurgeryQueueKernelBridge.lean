import Init
import Gnosis.Dewey300ThinTopology
import Gnosis.Dewey600ThinTopology
import Gnosis.GeometricErgodicity

/-!
# Dewey Bureaucracy/Surgery Queue Kernel Bridge

Dewey-300 bureaucracy latency and Dewey-600 thin surgery severance routed into
finite queue-boundary and kernel-lift witnesses.
-/

namespace DeweyBureaucracySurgeryQueueKernelBridge

structure BureaucracySetup where
  systemVelocity : Nat
  safeTolerance : Nat
  bureaucraticFriction : Nat
  hBureaucracy : systemVelocity + safeTolerance = bureaucraticFriction
  hSafe : 1 ≤ safeTolerance
deriving Repr

structure SurgerySetup where
  tumor : Nat
  sever : Nat
  hSever : sever = 0
deriving Repr

def deweyBureaucracySurgeryFailureBudget
    (bureaucracy : BureaucracySetup)
    (surgery : SurgerySetup) : Nat :=
  (bureaucracy.bureaucraticFriction - bureaucracy.systemVelocity) +
    surgery.sever

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

theorem bureaucracy_latency_from_source
    (bureaucracy : BureaucracySetup) :
    bureaucracy.systemVelocity ≤ bureaucracy.bureaucraticFriction := by
  exact Dewey300ThinTopology.dewey_350_bureaucracy_latency
    bureaucracy.systemVelocity
    bureaucracy.bureaucraticFriction
    (by
      rw [← bureaucracy.hBureaucracy]
      exact Nat.le_add_right
        bureaucracy.systemVelocity
        bureaucracy.safeTolerance)

theorem surgery_severance_from_source
    (surgery : SurgerySetup) :
    surgery.sever = 0 :=
  Dewey600ThinTopology.dewey_610_medicine_surgery
    surgery.tumor
    surgery.sever
    surgery.hSever

theorem bureaucracy_safe_tolerance_budget
    (bureaucracy : BureaucracySetup) :
    bureaucracy.bureaucraticFriction - bureaucracy.systemVelocity =
      bureaucracy.safeTolerance := by
  calc
    bureaucracy.bureaucraticFriction - bureaucracy.systemVelocity =
        (bureaucracy.systemVelocity + bureaucracy.safeTolerance) -
          bureaucracy.systemVelocity := by
      rw [bureaucracy.hBureaucracy]
    _ = bureaucracy.safeTolerance :=
      Nat.add_sub_cancel_left
        bureaucracy.systemVelocity
        bureaucracy.safeTolerance

theorem dewey_bureaucracy_surgery_budget_positive
    (bureaucracy : BureaucracySetup)
    (surgery : SurgerySetup) :
    0 < deweyBureaucracySurgeryFailureBudget bureaucracy surgery := by
  unfold deweyBureaucracySurgeryFailureBudget
  rw [bureaucracy_safe_tolerance_budget bureaucracy]
  exact Nat.lt_add_right surgery.sever bureaucracy.hSafe

theorem dewey_bureaucracy_surgery_budget_yields_unit_queue_boundary
    (bureaucracy : BureaucracySetup)
    (surgery : SurgerySetup) :
    bureaucracy.systemVelocity ≤ bureaucracy.bureaucraticFriction ∧
    surgery.sever = 0 ∧
    0 < deweyBureaucracySurgeryFailureBudget bureaucracy surgery ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate =
        deweyBureaucracySurgeryFailureBudget bureaucracy surgery ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount
            (deweyBureaucracySurgeryFailureBudget bureaucracy surgery))
          (deweyBureaucracySurgeryFailureBudget bureaucracy surgery) := by
  exact ⟨bureaucracy_latency_from_source bureaucracy,
    surgery_severance_from_source surgery,
    dewey_bureaucracy_surgery_budget_positive bureaucracy surgery,
    ⟨canonicalQueueBoundary
      (deweyBureaucracySurgeryFailureBudget bureaucracy surgery),
      rfl, rfl, rfl, rfl⟩⟩

theorem dewey_bureaucracy_surgery_budget_does_not_force_capacity_at_least_two
    (bureaucracy : BureaucracySetup)
    (surgery : SurgerySetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate =
          deweyBureaucracySurgeryFailureBudget bureaucracy surgery →
        boundary.serviceRate =
          quorumSize
            (replicaCount
              (deweyBureaucracySurgeryFailureBudget bureaucracy surgery))
            (deweyBureaucracySurgeryFailureBudget bureaucracy surgery) →
        2 ≤ boundary.capacity) := by
  intro hAll
  let boundary :=
    canonicalQueueBoundary
      (deweyBureaucracySurgeryFailureBudget bureaucracy surgery)
  have hCapacity : 2 ≤ 1 := hAll boundary rfl rfl
  exact (Nat.not_succ_le_self 1) hCapacity

theorem dewey_bureaucracy_surgery_semantic_morphism_boundary
    (bureaucracy : BureaucracySetup)
    (surgery : SurgerySetup)
    (interpret : Nat → Nat)
    (failureBudget : Nat)
    (hInterpret : interpret bureaucracy.safeTolerance = failureBudget)
    (hBudget :
      failureBudget =
        deweyBureaucracySurgeryFailureBudget bureaucracy surgery) :
    interpret bureaucracy.safeTolerance = failureBudget ∧
    failureBudget =
      deweyBureaucracySurgeryFailureBudget bureaucracy surgery ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = interpret bureaucracy.safeTolerance ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (interpret bureaucracy.safeTolerance))
          (interpret bureaucracy.safeTolerance) := by
  refine ⟨hInterpret, hBudget, ?_⟩
  exact ⟨canonicalQueueBoundary (interpret bureaucracy.safeTolerance),
    rfl, rfl, rfl, rfl⟩

theorem dewey_bureaucracy_surgery_budget_yields_geometric_rate_certificate
    (bureaucracy : BureaucracySetup)
    (surgery : SurgerySetup) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate
        (deweyBureaucracySurgeryFailureBudget bureaucracy surgery) ∧
      rate.initialBound =
        deweyBureaucracySurgeryFailureBudget bureaucracy surgery + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨budgetGeometricRate
    (deweyBureaucracySurgeryFailureBudget bureaucracy surgery),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate
      (deweyBureaucracySurgeryFailureBudget bureaucracy surgery)).hRateLtOne
  · exact (budgetGeometricRate
      (deweyBureaucracySurgeryFailureBudget bureaucracy surgery)).hInitialBoundPos

theorem dewey_bureaucracy_surgery_chapel_rate_initial_bound
    (bureaucracy : BureaucracySetup)
    (surgery : SurgerySetup) :
    (Gnosis.mkGeometricErgodicityRate
      3 4
      1 1
      1 1
      (deweyBureaucracySurgeryFailureBudget bureaucracy surgery + 1)
      (by decide)
      (by decide)
      (by decide)
      (by decide)
      (by decide)
      (by decide)
      (by decide)
      (Nat.succ_pos
        (deweyBureaucracySurgeryFailureBudget bureaucracy surgery))).initialBound =
      deweyBureaucracySurgeryFailureBudget bureaucracy surgery + 1 := by
  rfl

theorem dewey_bureaucracy_surgery_semantic_morphism_continuous_ergodicity_lift
    {Ω : Type}
    {maxQueue : Nat}
    (bureaucracy : BureaucracySetup)
    (surgery : SurgerySetup)
    (interpret : Nat → Nat)
    (failureBudget : Nat)
    (hInterpret : interpret bureaucracy.safeTolerance = failureBudget)
    (hBudget :
      failureBudget =
        deweyBureaucracySurgeryFailureBudget bureaucracy surgery)
    (embedding : Gnosis.DiscreteSubLatticeEmbedding Ω maxQueue)
    (witness : Gnosis.GeometricErgodicWitness maxQueue)
    (hKernelMatch : witness.envelope.kernel = embedding.discreteKernel) :
    bureaucracy.systemVelocity ≤ bureaucracy.bureaucraticFriction ∧
    surgery.sever = 0 ∧
    interpret bureaucracy.safeTolerance = failureBudget ∧
    failureBudget =
      deweyBureaucracySurgeryFailureBudget bureaucracy surgery ∧
    embedding.continuousKernel.fosterDrift ∧
    0 < embedding.continuousKernel.driftGap ∧
    witness.rate.rateNumerator < witness.rate.rateDenominator := by
  have hLift :=
    Gnosis.continuous_ergodicity_lift embedding witness hKernelMatch
  exact ⟨bureaucracy_latency_from_source bureaucracy,
    surgery_severance_from_source surgery,
    hInterpret,
    hBudget,
    hLift.1,
    hLift.2.1,
    hLift.2.2⟩

end DeweyBureaucracySurgeryQueueKernelBridge
