import Init
import Gnosis.GeometricErgodicity

/-!
# Humor/Tensegrity Queue Kernel Bridge

Finite setup-complexity and tensegrity-surplus witnesses for stale
humor+tensegrity MCP rows, including a chapel witness compiler.
-/

namespace HumorTensegrityQueueKernelBridge

structure HumorSetup where
  complexity : Nat
  hComplexity : 1 ≤ complexity
deriving Repr

structure TensegritySetup where
  visibleNodes : Nat
  invisibleTension : Nat
  integrity : Nat
  hTension : visibleNodes < invisibleTension
  hIntegrity : integrity = visibleNodes + invisibleTension
deriving Repr

def tensegritySurplus (tensegrity : TensegritySetup) : Nat :=
  tensegrity.invisibleTension - tensegrity.visibleNodes

def humorTensegrityFailureBudget
    (humor : HumorSetup)
    (tensegrity : TensegritySetup) : Nat :=
  humor.complexity + tensegritySurplus tensegrity

def replicaCount (budget : Nat) : Nat := 2 * budget + 1

def quorumSize (_replicas budget : Nat) : Nat := budget + 1

def topologicalDeficit (paths streams : Nat) : Nat := paths - streams

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

theorem tensegrity_surplus_positive
    (tensegrity : TensegritySetup) :
    0 < tensegritySurplus tensegrity := by
  unfold tensegritySurplus
  exact Nat.sub_pos_of_lt tensegrity.hTension

theorem humor_tensegrity_budget_positive
    (humor : HumorSetup)
    (tensegrity : TensegritySetup) :
    0 < humorTensegrityFailureBudget humor tensegrity := by
  unfold humorTensegrityFailureBudget
  exact Nat.lt_add_right
    (tensegritySurplus tensegrity)
    humor.hComplexity

theorem humor_tensegrity_budget_yields_unit_queue_boundary
    (humor : HumorSetup)
    (tensegrity : TensegritySetup) :
    0 < humor.complexity ∧
    tensegrity.visibleNodes < tensegrity.invisibleTension ∧
    tensegrity.integrity =
      tensegrity.visibleNodes + tensegrity.invisibleTension ∧
    0 < humorTensegrityFailureBudget humor tensegrity ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate =
        humorTensegrityFailureBudget humor tensegrity ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (humorTensegrityFailureBudget humor tensegrity))
          (humorTensegrityFailureBudget humor tensegrity) := by
  exact ⟨humor.hComplexity, tensegrity.hTension, tensegrity.hIntegrity,
    humor_tensegrity_budget_positive humor tensegrity,
    ⟨canonicalQueueBoundary (humorTensegrityFailureBudget humor tensegrity),
      rfl, rfl, rfl, rfl⟩⟩

theorem humor_tensegrity_budget_yields_positive_topological_deficit
    (humor : HumorSetup)
    (tensegrity : TensegritySetup) :
    0 < topologicalDeficit
      (humorTensegrityFailureBudget humor tensegrity + 1) 1 := by
  unfold topologicalDeficit
  rw [Nat.add_sub_cancel]
  exact humor_tensegrity_budget_positive humor tensegrity

theorem humor_tensegrity_budget_does_not_force_service_surplus_two
    (humor : HumorSetup)
    (tensegrity : TensegritySetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate =
          humorTensegrityFailureBudget humor tensegrity →
        boundary.serviceRate =
          quorumSize
            (replicaCount (humorTensegrityFailureBudget humor tensegrity))
            (humorTensegrityFailureBudget humor tensegrity) →
        boundary.arrivalRate + 2 ≤ boundary.serviceRate) := by
  intro hAll
  let budget := humorTensegrityFailureBudget humor tensegrity
  let boundary := canonicalQueueBoundary budget
  have hSlack : budget + 2 ≤ budget + 1 := hAll boundary rfl rfl
  exact (Nat.not_succ_le_self (budget + 1)) hSlack

theorem humor_tensegrity_budget_does_not_force_strict_capacity_growth
    (humor : HumorSetup)
    (tensegrity : TensegritySetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate =
          humorTensegrityFailureBudget humor tensegrity →
        boundary.serviceRate =
          quorumSize
            (replicaCount (humorTensegrityFailureBudget humor tensegrity))
            (humorTensegrityFailureBudget humor tensegrity) →
        1 < boundary.capacity) := by
  intro hAll
  let boundary := canonicalQueueBoundary
    (humorTensegrityFailureBudget humor tensegrity)
  exact Nat.lt_irrefl 1 (hAll boundary rfl rfl)

theorem humor_tensegrity_semantic_morphism_yields_unit_queue_boundary
    (humor : HumorSetup)
    (tensegrity : TensegritySetup)
    (interpret : Nat → Nat)
    (hInterpret :
      interpret (humorTensegrityFailureBudget humor tensegrity) =
        humorTensegrityFailureBudget humor tensegrity) :
    interpret (humorTensegrityFailureBudget humor tensegrity) =
      humorTensegrityFailureBudget humor tensegrity ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate =
        interpret (humorTensegrityFailureBudget humor tensegrity) ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount
            (interpret (humorTensegrityFailureBudget humor tensegrity)))
          (interpret (humorTensegrityFailureBudget humor tensegrity)) := by
  refine ⟨hInterpret, ?_⟩
  exact ⟨canonicalQueueBoundary
      (interpret (humorTensegrityFailureBudget humor tensegrity)),
    rfl, rfl, rfl, rfl⟩

theorem humor_tensegrity_budget_yields_geometric_rate_certificate
    (humor : HumorSetup)
    (tensegrity : TensegritySetup) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate
        (humorTensegrityFailureBudget humor tensegrity) ∧
      rate.initialBound =
        humorTensegrityFailureBudget humor tensegrity + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨budgetGeometricRate
    (humorTensegrityFailureBudget humor tensegrity),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate
      (humorTensegrityFailureBudget humor tensegrity)).hRateLtOne
  · exact (budgetGeometricRate
      (humorTensegrityFailureBudget humor tensegrity)).hInitialBoundPos

theorem humor_tensegrity_semantic_morphism_continuous_ergodicity_lift
    {Ω : Type}
    {maxQueue : Nat}
    (humor : HumorSetup)
    (tensegrity : TensegritySetup)
    (interpret : Nat → Nat)
    (hInterpret :
      interpret (humorTensegrityFailureBudget humor tensegrity) =
        humorTensegrityFailureBudget humor tensegrity)
    (embedding : Gnosis.DiscreteSubLatticeEmbedding Ω maxQueue)
    (witness : Gnosis.GeometricErgodicWitness maxQueue)
    (hKernelMatch : witness.envelope.kernel = embedding.discreteKernel) :
    0 < humor.complexity ∧
    tensegrity.visibleNodes < tensegrity.invisibleTension ∧
    tensegrity.integrity =
      tensegrity.visibleNodes + tensegrity.invisibleTension ∧
    interpret (humorTensegrityFailureBudget humor tensegrity) =
      humorTensegrityFailureBudget humor tensegrity ∧
    embedding.continuousKernel.fosterDrift ∧
    0 < embedding.continuousKernel.driftGap ∧
    witness.rate.rateNumerator < witness.rate.rateDenominator := by
  have hLift :=
    Gnosis.continuous_ergodicity_lift embedding witness hKernelMatch
  exact ⟨humor.hComplexity, tensegrity.hTension, tensegrity.hIntegrity,
    hInterpret, hLift.1, hLift.2.1, hLift.2.2⟩

structure PrimitiveKernelObligations (maxQueue : Nat) where
  kernel : Gnosis.CountableCertifiedKernel maxQueue
  atom : Nat
  hAtomInRange : atom ≤ maxQueue
  stepNumerator : Nat
  stepDenominator : Nat
  smallSetNumerator : Nat
  smallSetDenominator : Nat
  hStepPos : 0 < stepNumerator
  hSmallSetPos : 0 < smallSetNumerator
  hStepDenomPos : 0 < stepDenominator
  hSmallSetDenomPos : 0 < smallSetDenominator
  hStepBound : stepNumerator ≤ stepDenominator
  hSmallSetBound : smallSetNumerator ≤ smallSetDenominator

def compiledWitness
    {maxQueue : Nat}
    (humor : HumorSetup)
    (tensegrity : TensegritySetup)
    (primitives : PrimitiveKernelObligations maxQueue) :
    Gnosis.GeometricErgodicWitness maxQueue :=
  { envelope :=
      { kernel := primitives.kernel
        atom := primitives.atom
        stepNumerator := primitives.stepNumerator
        stepDenominator := primitives.stepDenominator
        smallSetNumerator := primitives.smallSetNumerator
        smallSetDenominator := primitives.smallSetDenominator
        hStepPos := primitives.hStepPos
        hSmallSetPos := primitives.hSmallSetPos
        hStepDenomPos := primitives.hStepDenomPos
        hSmallSetDenomPos := primitives.hSmallSetDenomPos
        hStepBound := primitives.hStepBound
        hSmallSetBound := primitives.hSmallSetBound
        hAtomInRange := primitives.hAtomInRange }
    rate :=
      Gnosis.mkGeometricErgodicityRate
        3 4
        primitives.stepNumerator
        primitives.stepDenominator
        primitives.smallSetNumerator
        primitives.smallSetDenominator
        (humorTensegrityFailureBudget humor tensegrity + 1)
        (by decide)
        (by decide)
        (by decide)
        primitives.hStepPos
        primitives.hStepDenomPos
        primitives.hSmallSetPos
        primitives.hSmallSetDenomPos
        (Nat.succ_pos (humorTensegrityFailureBudget humor tensegrity))
    hRateConsistent := ⟨rfl, rfl⟩ }

theorem humor_tensegrity_compile_witness_from_primitives
    {maxQueue : Nat}
    (humor : HumorSetup)
    (tensegrity : TensegritySetup)
    (primitives : PrimitiveKernelObligations maxQueue) :
    let witness := compiledWitness humor tensegrity primitives
    witness.envelope.kernel = primitives.kernel ∧
    witness.envelope.atom = primitives.atom ∧
    witness.rate.initialBound =
      humorTensegrityFailureBudget humor tensegrity + 1 ∧
    witness.rate.rateNumerator = 3 ∧
    witness.rate.rateDenominator = 4 ∧
    witness.rate.rateNumerator < witness.rate.rateDenominator ∧
    0 < witness.rate.initialBound ∧
    0 < witness.envelope.stepNumerator ∧
    0 < witness.envelope.smallSetNumerator := by
  intro witness
  exact ⟨rfl, rfl, rfl, rfl, rfl,
    witness.rate.hRateLtOne,
    witness.rate.hInitialBoundPos,
    witness.envelope.hStepPos,
    witness.envelope.hSmallSetPos⟩

theorem humor_tensegrity_compiled_witness_continuous_ergodicity_lift
    {Ω : Type}
    {maxQueue : Nat}
    (humor : HumorSetup)
    (tensegrity : TensegritySetup)
    (primitives : PrimitiveKernelObligations maxQueue)
    (embedding : Gnosis.DiscreteSubLatticeEmbedding Ω maxQueue)
    (hKernelMatch : primitives.kernel = embedding.discreteKernel) :
    let witness := compiledWitness humor tensegrity primitives
    witness.envelope.kernel = embedding.discreteKernel ∧
    embedding.continuousKernel.fosterDrift ∧
    0 < embedding.continuousKernel.driftGap ∧
    witness.rate.rateNumerator < witness.rate.rateDenominator := by
  intro witness
  have hWitnessKernel : witness.envelope.kernel = embedding.discreteKernel := by
    rw [show witness.envelope.kernel = primitives.kernel by rfl]
    exact hKernelMatch
  have hLift :=
    Gnosis.continuous_ergodicity_lift embedding witness hWitnessKernel
  exact ⟨hWitnessKernel, hLift.1, hLift.2.1, hLift.2.2⟩

end HumorTensegrityQueueKernelBridge
