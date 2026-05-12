import Init
import Gnosis.GeometricErgodicity

/-!
# Quorum/Sleep/Crypto Queue Kernel Bridge

Finite quorum-history, weighted sleep-debt, and cryptographic side-channel
witnesses for stale MCP rows.
-/

namespace QuorumSleepCryptoQueueKernelBridge

structure QuorumHistory where
  depth : Nat
  hNonempty : 0 < depth
deriving Repr

structure WeightedSleepDebt where
  thresholdRhs : Nat
  thresholdLhs : Nat
  iterations : Nat
  iteratedDebt : Nat
  hThreshold : thresholdRhs < thresholdLhs
  hIterations : 0 < iterations
  hDebt : 0 < iteratedDebt
deriving Repr

structure SideChannelShadow where
  perEvalFloor : Nat
  hFloor : 0 < perEvalFloor
deriving Repr

def quorumSleepCryptoFailureBudget
    (history : QuorumHistory)
    (sleep : WeightedSleepDebt)
    (crypto : SideChannelShadow) : Nat :=
  history.depth + sleep.iteratedDebt + crypto.perEvalFloor

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

theorem quorum_sleep_crypto_budget_positive
    (history : QuorumHistory)
    (sleep : WeightedSleepDebt)
    (crypto : SideChannelShadow) :
    0 < quorumSleepCryptoFailureBudget history sleep crypto := by
  unfold quorumSleepCryptoFailureBudget
  rw [Nat.add_assoc]
  exact Nat.lt_add_right
    (sleep.iteratedDebt + crypto.perEvalFloor)
    history.hNonempty

theorem quorum_sleep_crypto_budget_yields_unit_queue_boundary
    (history : QuorumHistory)
    (sleep : WeightedSleepDebt)
    (crypto : SideChannelShadow) :
    0 < history.depth ∧
    sleep.thresholdRhs < sleep.thresholdLhs ∧
    0 < sleep.iterations ∧
    0 < sleep.iteratedDebt ∧
    0 < crypto.perEvalFloor ∧
    0 < quorumSleepCryptoFailureBudget history sleep crypto ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate =
        quorumSleepCryptoFailureBudget history sleep crypto ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (quorumSleepCryptoFailureBudget history sleep crypto))
          (quorumSleepCryptoFailureBudget history sleep crypto) := by
  exact ⟨history.hNonempty, sleep.hThreshold, sleep.hIterations, sleep.hDebt,
    crypto.hFloor, quorum_sleep_crypto_budget_positive history sleep crypto,
    ⟨canonicalQueueBoundary (quorumSleepCryptoFailureBudget history sleep crypto),
      rfl, rfl, rfl, rfl⟩⟩

theorem quorum_sleep_crypto_budget_yields_positive_topological_deficit
    (history : QuorumHistory)
    (sleep : WeightedSleepDebt)
    (crypto : SideChannelShadow) :
    0 < topologicalDeficit
      (quorumSleepCryptoFailureBudget history sleep crypto + 1) 1 := by
  unfold topologicalDeficit
  rw [Nat.add_sub_cancel]
  exact quorum_sleep_crypto_budget_positive history sleep crypto

theorem quorum_sleep_crypto_budget_does_not_force_positive_beta1
    (history : QuorumHistory)
    (sleep : WeightedSleepDebt)
    (crypto : SideChannelShadow) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate =
          quorumSleepCryptoFailureBudget history sleep crypto →
        boundary.serviceRate =
          quorumSize
            (replicaCount (quorumSleepCryptoFailureBudget history sleep crypto))
            (quorumSleepCryptoFailureBudget history sleep crypto) →
        0 < boundary.beta1) := by
  intro hAll
  let boundary := canonicalQueueBoundary
    (quorumSleepCryptoFailureBudget history sleep crypto)
  exact Nat.lt_irrefl 0 (hAll boundary rfl rfl)

theorem quorum_sleep_crypto_budget_does_not_force_strict_capacity_growth
    (history : QuorumHistory)
    (sleep : WeightedSleepDebt)
    (crypto : SideChannelShadow) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate =
          quorumSleepCryptoFailureBudget history sleep crypto →
        boundary.serviceRate =
          quorumSize
            (replicaCount (quorumSleepCryptoFailureBudget history sleep crypto))
            (quorumSleepCryptoFailureBudget history sleep crypto) →
        2 ≤ boundary.capacity) := by
  intro hAll
  let boundary := canonicalQueueBoundary
    (quorumSleepCryptoFailureBudget history sleep crypto)
  have hCapacity : 2 ≤ 1 := hAll boundary rfl rfl
  exact (Nat.not_succ_le_self 1) hCapacity

theorem quorum_sleep_crypto_budget_yields_geometric_rate_certificate
    (history : QuorumHistory)
    (sleep : WeightedSleepDebt)
    (crypto : SideChannelShadow) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate
        (quorumSleepCryptoFailureBudget history sleep crypto) ∧
      rate.initialBound =
        quorumSleepCryptoFailureBudget history sleep crypto + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨budgetGeometricRate
      (quorumSleepCryptoFailureBudget history sleep crypto),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate
      (quorumSleepCryptoFailureBudget history sleep crypto)).hRateLtOne
  · exact (budgetGeometricRate
      (quorumSleepCryptoFailureBudget history sleep crypto)).hInitialBoundPos

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
    (history : QuorumHistory)
    (sleep : WeightedSleepDebt)
    (crypto : SideChannelShadow)
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
        (quorumSleepCryptoFailureBudget history sleep crypto + 1)
        (by decide)
        (by decide)
        (by decide)
        primitives.hStepPos
        primitives.hStepDenomPos
        primitives.hSmallSetPos
        primitives.hSmallSetDenomPos
        (Nat.succ_pos (quorumSleepCryptoFailureBudget history sleep crypto))
    hRateConsistent := ⟨rfl, rfl⟩ }

theorem quorum_sleep_crypto_compile_witness_from_primitives
    {maxQueue : Nat}
    (history : QuorumHistory)
    (sleep : WeightedSleepDebt)
    (crypto : SideChannelShadow)
    (primitives : PrimitiveKernelObligations maxQueue) :
    let witness := compiledWitness history sleep crypto primitives
    witness.envelope.kernel = primitives.kernel ∧
    witness.rate.initialBound =
      quorumSleepCryptoFailureBudget history sleep crypto + 1 ∧
    witness.rate.rateNumerator = 3 ∧
    witness.rate.rateDenominator = 4 ∧
    witness.rate.rateNumerator < witness.rate.rateDenominator ∧
    0 < witness.rate.initialBound ∧
    0 < witness.envelope.stepNumerator ∧
    0 < witness.envelope.smallSetNumerator := by
  intro witness
  exact ⟨rfl, rfl, rfl, rfl,
    witness.rate.hRateLtOne,
    witness.rate.hInitialBoundPos,
    witness.envelope.hStepPos,
    witness.envelope.hSmallSetPos⟩

theorem quorum_sleep_crypto_compiled_witness_continuous_ergodicity_lift
    {Ω : Type}
    {maxQueue : Nat}
    (history : QuorumHistory)
    (sleep : WeightedSleepDebt)
    (crypto : SideChannelShadow)
    (primitives : PrimitiveKernelObligations maxQueue)
    (embedding : Gnosis.DiscreteSubLatticeEmbedding Ω maxQueue)
    (hKernelMatch : primitives.kernel = embedding.discreteKernel) :
    let witness := compiledWitness history sleep crypto primitives
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

end QuorumSleepCryptoQueueKernelBridge
