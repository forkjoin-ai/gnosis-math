import Init
import Gnosis.GeometricErgodicity
import Gnosis.Bridges.CacheAsyncFrfQueueKernelBridge

/-!
# Cache/Async/Sleep Queue Kernel Bridge

Finite cache cold-path, async durability-vent, and weighted sleep-debt
witnesses for stale MCP rows.
-/

namespace CacheAsyncSleepQueueKernelBridge

abbrev CacheColdPath := CacheAsyncFrfQueueKernelBridge.CacheColdPath
abbrev AsyncProfile := CacheAsyncFrfQueueKernelBridge.AsyncProfile
abbrev AsyncDurabilityStep := CacheAsyncFrfQueueKernelBridge.AsyncDurabilityStep

structure WeightedSleepDebt where
  thresholdRhs : Nat
  thresholdLhs : Nat
  iterations : Nat
  iteratedDebt : Nat
  hThreshold : thresholdRhs < thresholdLhs
  hIterations : 0 < iterations
  hDebt : 0 < iteratedDebt
deriving Repr

def cacheAsyncSleepFailureBudget
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (sleep : WeightedSleepDebt) : Nat :=
  cache.traceFoldCold + async.current.totalVent + sleep.iteratedDebt

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

theorem cache_async_sleep_budget_positive
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (sleep : WeightedSleepDebt) :
    0 < cacheAsyncSleepFailureBudget cache async sleep := by
  unfold cacheAsyncSleepFailureBudget
  rw [Nat.add_assoc]
  exact Nat.lt_add_right
    (async.current.totalVent + sleep.iteratedDebt)
    cache.hCold

theorem cache_async_sleep_budget_yields_unit_queue_boundary
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (sleep : WeightedSleepDebt) :
    async.previous.userFork = async.current.userFork ∧
    async.previous.userVent = async.current.userVent ∧
    async.current.bgVent =
      async.previous.bgVent + async.backgroundDelta ∧
    async.current.totalVent =
      async.previous.totalVent + async.backgroundDelta ∧
    sleep.thresholdRhs < sleep.thresholdLhs ∧
    0 < sleep.iterations ∧
    cache.traceFoldCold = cache.escCanonMiss ∧
    0 < cacheAsyncSleepFailureBudget cache async sleep ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = cacheAsyncSleepFailureBudget cache async sleep ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (cacheAsyncSleepFailureBudget cache async sleep))
          (cacheAsyncSleepFailureBudget cache async sleep) := by
  exact ⟨async.hUserFork, async.hUserVent, async.hBgVent, async.hTotalVent,
    sleep.hThreshold, sleep.hIterations, cache.hTrace,
    cache_async_sleep_budget_positive cache async sleep,
    ⟨canonicalQueueBoundary (cacheAsyncSleepFailureBudget cache async sleep),
      rfl, rfl, rfl, rfl⟩⟩

theorem cache_async_sleep_budget_yields_positive_topological_deficit
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (sleep : WeightedSleepDebt) :
    0 < topologicalDeficit
      (cacheAsyncSleepFailureBudget cache async sleep + 1) 1 := by
  unfold topologicalDeficit
  rw [Nat.add_sub_cancel]
  exact cache_async_sleep_budget_positive cache async sleep

theorem cache_async_sleep_budget_does_not_force_beta1_equals_budget
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (sleep : WeightedSleepDebt) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = cacheAsyncSleepFailureBudget cache async sleep →
        boundary.serviceRate =
          quorumSize
            (replicaCount (cacheAsyncSleepFailureBudget cache async sleep))
            (cacheAsyncSleepFailureBudget cache async sleep) →
        boundary.beta1 = cacheAsyncSleepFailureBudget cache async sleep) := by
  intro hAll
  let boundary := canonicalQueueBoundary
    (cacheAsyncSleepFailureBudget cache async sleep)
  have hEq : boundary.beta1 = cacheAsyncSleepFailureBudget cache async sleep :=
    hAll boundary rfl rfl
  have hPositive : 0 < cacheAsyncSleepFailureBudget cache async sleep :=
    cache_async_sleep_budget_positive cache async sleep
  rw [show boundary.beta1 = 0 by rfl] at hEq
  rw [← hEq] at hPositive
  exact Nat.lt_irrefl 0 hPositive

theorem cache_async_sleep_semantic_morphism_yields_positive_topological_deficit
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (sleep : WeightedSleepDebt)
    (interpret : Nat → Nat)
    (hInterpret :
      interpret (cacheAsyncSleepFailureBudget cache async sleep + 1) =
        cacheAsyncSleepFailureBudget cache async sleep + 1) :
    0 < topologicalDeficit
      (interpret (cacheAsyncSleepFailureBudget cache async sleep + 1)) 1 := by
  rw [hInterpret]
  exact cache_async_sleep_budget_yields_positive_topological_deficit
    cache async sleep

theorem cache_async_sleep_budget_yields_boundary_and_positive_deficit
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (sleep : WeightedSleepDebt) :
    (∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = cacheAsyncSleepFailureBudget cache async sleep ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (cacheAsyncSleepFailureBudget cache async sleep))
          (cacheAsyncSleepFailureBudget cache async sleep)) ∧
    0 < topologicalDeficit
      (cacheAsyncSleepFailureBudget cache async sleep + 1) 1 := by
  refine ⟨?_, cache_async_sleep_budget_yields_positive_topological_deficit cache async sleep⟩
  exact ⟨canonicalQueueBoundary (cacheAsyncSleepFailureBudget cache async sleep),
    rfl, rfl, rfl, rfl⟩

structure RetrialQueueKernelFamily where
  maxQueue : Nat
  maxOrbit : Nat
  stationaryBalance : Bool
  terminalBalance : Bool
deriving Repr

structure CacheAsyncSleepRetrialAdapter where
  cache : CacheColdPath
  async : AsyncDurabilityStep
  sleep : WeightedSleepDebt
  kernel : RetrialQueueKernelFamily
  budget : Nat
  hBudgetEq : budget = cacheAsyncSleepFailureBudget cache async sleep
deriving Repr

namespace CacheAsyncSleepRetrialAdapter

theorem retrial_stationary_balance_bridge
    (adapter : CacheAsyncSleepRetrialAdapter) :
    adapter.budget =
      cacheAsyncSleepFailureBudget adapter.cache adapter.async adapter.sleep ∧
    0 < adapter.budget ∧
    adapter.kernel.stationaryBalance = adapter.kernel.stationaryBalance ∧
    adapter.kernel.terminalBalance = adapter.kernel.terminalBalance := by
  rw [adapter.hBudgetEq]
  exact ⟨rfl,
    cache_async_sleep_budget_positive adapter.cache adapter.async adapter.sleep,
    rfl,
    rfl⟩

end CacheAsyncSleepRetrialAdapter

theorem cache_async_sleep_delta_budget_yields_unit_queue_boundary
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (sleep : WeightedSleepDebt) :
    async.current.bgVent =
      async.previous.bgVent + async.backgroundDelta ∧
    0 < cacheAsyncSleepFailureBudget cache async sleep ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = cacheAsyncSleepFailureBudget cache async sleep ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (cacheAsyncSleepFailureBudget cache async sleep))
          (cacheAsyncSleepFailureBudget cache async sleep) := by
  exact ⟨async.hBgVent,
    cache_async_sleep_budget_positive cache async sleep,
    ⟨canonicalQueueBoundary (cacheAsyncSleepFailureBudget cache async sleep),
      rfl, rfl, rfl, rfl⟩⟩

theorem cache_async_sleep_delta_budget_yields_positive_topological_deficit
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (sleep : WeightedSleepDebt) :
    0 < topologicalDeficit
      (cacheAsyncSleepFailureBudget cache async sleep + 1) 1 :=
  cache_async_sleep_budget_yields_positive_topological_deficit cache async sleep

theorem cache_async_sleep_delta_budget_yields_boundary_and_positive_deficit
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (sleep : WeightedSleepDebt) :
    (∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = cacheAsyncSleepFailureBudget cache async sleep ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (cacheAsyncSleepFailureBudget cache async sleep))
          (cacheAsyncSleepFailureBudget cache async sleep)) ∧
    0 < topologicalDeficit
      (cacheAsyncSleepFailureBudget cache async sleep + 1) 1 :=
  cache_async_sleep_budget_yields_boundary_and_positive_deficit cache async sleep

theorem cache_async_sleep_delta_budget_does_not_force_beta1_equals_budget
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (sleep : WeightedSleepDebt) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = cacheAsyncSleepFailureBudget cache async sleep →
        boundary.serviceRate =
          quorumSize
            (replicaCount (cacheAsyncSleepFailureBudget cache async sleep))
            (cacheAsyncSleepFailureBudget cache async sleep) →
        boundary.beta1 = cacheAsyncSleepFailureBudget cache async sleep) :=
  cache_async_sleep_budget_does_not_force_beta1_equals_budget cache async sleep

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
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (sleep : WeightedSleepDebt)
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
        (cacheAsyncSleepFailureBudget cache async sleep + 1)
        (by decide)
        (by decide)
        (by decide)
        primitives.hStepPos
        primitives.hStepDenomPos
        primitives.hSmallSetPos
        primitives.hSmallSetDenomPos
        (Nat.succ_pos (cacheAsyncSleepFailureBudget cache async sleep))
    hRateConsistent := ⟨rfl, rfl⟩ }

theorem cache_async_sleep_compile_witness_from_primitives
    {maxQueue : Nat}
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (sleep : WeightedSleepDebt)
    (primitives : PrimitiveKernelObligations maxQueue) :
    let witness := compiledWitness cache async sleep primitives
    witness.envelope.kernel = primitives.kernel ∧
    witness.rate.initialBound =
      cacheAsyncSleepFailureBudget cache async sleep + 1 ∧
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

theorem cache_async_sleep_compiled_witness_continuous_ergodicity_lift
    {Ω : Type}
    {maxQueue : Nat}
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (sleep : WeightedSleepDebt)
    (primitives : PrimitiveKernelObligations maxQueue)
    (embedding : Gnosis.DiscreteSubLatticeEmbedding Ω maxQueue)
    (hKernelMatch : primitives.kernel = embedding.discreteKernel) :
    let witness := compiledWitness cache async sleep primitives
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

theorem cache_async_sleep_delta_compile_witness_from_primitives
    {maxQueue : Nat}
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (sleep : WeightedSleepDebt)
    (primitives : PrimitiveKernelObligations maxQueue) :
    let witness := compiledWitness cache async sleep primitives
    async.current.bgVent =
      async.previous.bgVent + async.backgroundDelta ∧
    witness.envelope.kernel = primitives.kernel ∧
    witness.rate.initialBound =
      cacheAsyncSleepFailureBudget cache async sleep + 1 ∧
    witness.rate.rateNumerator < witness.rate.rateDenominator := by
  intro witness
  exact ⟨async.hBgVent, rfl, rfl, witness.rate.hRateLtOne⟩

theorem cache_async_sleep_delta_compiled_witness_continuous_ergodicity_lift
    {Ω : Type}
    {maxQueue : Nat}
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (sleep : WeightedSleepDebt)
    (primitives : PrimitiveKernelObligations maxQueue)
    (embedding : Gnosis.DiscreteSubLatticeEmbedding Ω maxQueue)
    (hKernelMatch : primitives.kernel = embedding.discreteKernel) :
    let witness := compiledWitness cache async sleep primitives
    async.current.bgVent =
      async.previous.bgVent + async.backgroundDelta ∧
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
  exact ⟨async.hBgVent, hWitnessKernel, hLift.1, hLift.2.1, hLift.2.2⟩

end CacheAsyncSleepQueueKernelBridge
