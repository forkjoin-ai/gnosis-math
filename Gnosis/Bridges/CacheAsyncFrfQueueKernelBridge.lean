import Init
import Gnosis.GeometricErgodicity

/-!
# Cache/Async/FRF Queue Kernel Bridge

Finite cache cold-path, async durability-vent, and FRF race witnesses for stale
MCP queue/kernel rows.
-/

namespace CacheAsyncFrfQueueKernelBridge

structure CacheColdPath where
  traceFoldCold : Nat
  escCanonMiss : Nat
  hTrace : traceFoldCold = escCanonMiss
  hCold : 0 < traceFoldCold
deriving Repr

structure AsyncProfile where
  userFork : Nat
  userVent : Nat
  bgVent : Nat
  totalVent : Nat
  hTotalVent : totalVent = userFork + userVent + bgVent
deriving Repr

structure AsyncDurabilityStep where
  previous : AsyncProfile
  current : AsyncProfile
  backgroundDelta : Nat
  hUserFork : previous.userFork = current.userFork
  hUserVent : previous.userVent = current.userVent
  hBgVent : current.bgVent = previous.bgVent + backgroundDelta
  hTotalVent : current.totalVent = previous.totalVent + backgroundDelta
deriving Repr

structure FrfWitness where
  raceMass : Nat
  hRace : raceMass = 3
deriving Repr

def cacheAsyncFailureBudget
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep) : Nat :=
  cache.traceFoldCold + async.current.totalVent

def cacheAsyncFrfFailureBudget
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (frf : FrfWitness) : Nat :=
  cache.traceFoldCold + async.current.totalVent + frf.raceMass

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

theorem cache_async_budget_positive
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep) :
    0 < cacheAsyncFailureBudget cache async := by
  unfold cacheAsyncFailureBudget
  exact Nat.lt_add_right async.current.totalVent cache.hCold

theorem cache_async_frf_budget_positive
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (frf : FrfWitness) :
    0 < cacheAsyncFrfFailureBudget cache async frf := by
  unfold cacheAsyncFrfFailureBudget
  rw [Nat.add_assoc]
  exact Nat.lt_add_right
    (async.current.totalVent + frf.raceMass)
    cache.hCold

theorem cache_async_budget_yields_unit_queue_boundary
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep) :
    async.previous.userFork = async.current.userFork ∧
    async.previous.userVent = async.current.userVent ∧
    async.current.bgVent =
      async.previous.bgVent + async.backgroundDelta ∧
    cache.traceFoldCold = cache.escCanonMiss ∧
    async.current.totalVent =
      async.previous.totalVent + async.backgroundDelta ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = cacheAsyncFailureBudget cache async ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (cacheAsyncFailureBudget cache async))
          (cacheAsyncFailureBudget cache async) := by
  exact ⟨async.hUserFork, async.hUserVent, async.hBgVent, cache.hTrace,
    async.hTotalVent,
    ⟨canonicalQueueBoundary (cacheAsyncFailureBudget cache async),
      rfl, rfl, rfl, rfl⟩⟩

theorem cache_async_frf_budget_yields_unit_queue_boundary
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (frf : FrfWitness) :
    async.previous.userFork = async.current.userFork ∧
    async.previous.userVent = async.current.userVent ∧
    async.current.bgVent =
      async.previous.bgVent + async.backgroundDelta ∧
    cache.traceFoldCold = cache.escCanonMiss ∧
    frf.raceMass = 3 ∧
    0 < cacheAsyncFrfFailureBudget cache async frf ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = cacheAsyncFrfFailureBudget cache async frf ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (cacheAsyncFrfFailureBudget cache async frf))
          (cacheAsyncFrfFailureBudget cache async frf) := by
  exact ⟨async.hUserFork, async.hUserVent, async.hBgVent, cache.hTrace,
    frf.hRace, cache_async_frf_budget_positive cache async frf,
    ⟨canonicalQueueBoundary (cacheAsyncFrfFailureBudget cache async frf),
      rfl, rfl, rfl, rfl⟩⟩

theorem cache_async_frf_budget_does_not_force_strict_capacity_growth
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (frf : FrfWitness) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = cacheAsyncFrfFailureBudget cache async frf →
        boundary.serviceRate =
          quorumSize
            (replicaCount (cacheAsyncFrfFailureBudget cache async frf))
            (cacheAsyncFrfFailureBudget cache async frf) →
        1 < boundary.capacity) := by
  intro hAll
  let boundary := canonicalQueueBoundary
    (cacheAsyncFrfFailureBudget cache async frf)
  exact Nat.lt_irrefl 1 (hAll boundary rfl rfl)

theorem cache_async_frf_budget_does_not_force_beta1_equals_budget
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (frf : FrfWitness) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = cacheAsyncFrfFailureBudget cache async frf →
        boundary.serviceRate =
          quorumSize
            (replicaCount (cacheAsyncFrfFailureBudget cache async frf))
            (cacheAsyncFrfFailureBudget cache async frf) →
        boundary.beta1 = cacheAsyncFrfFailureBudget cache async frf) := by
  intro hAll
  let boundary := canonicalQueueBoundary
    (cacheAsyncFrfFailureBudget cache async frf)
  have hEq : boundary.beta1 = cacheAsyncFrfFailureBudget cache async frf :=
    hAll boundary rfl rfl
  have hPositive : 0 < cacheAsyncFrfFailureBudget cache async frf :=
    cache_async_frf_budget_positive cache async frf
  rw [show boundary.beta1 = 0 by rfl] at hEq
  rw [← hEq] at hPositive
  exact Nat.lt_irrefl 0 hPositive

theorem cache_async_frf_semantic_morphism_yields_unit_queue_boundary
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (frf : FrfWitness)
    (interpret : Nat → Nat)
    (hInterpret :
      interpret (cacheAsyncFrfFailureBudget cache async frf) =
        cacheAsyncFrfFailureBudget cache async frf) :
    interpret (cacheAsyncFrfFailureBudget cache async frf) =
      cacheAsyncFrfFailureBudget cache async frf ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate =
        interpret (cacheAsyncFrfFailureBudget cache async frf) ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount
            (interpret (cacheAsyncFrfFailureBudget cache async frf)))
          (interpret (cacheAsyncFrfFailureBudget cache async frf)) := by
  refine ⟨hInterpret, ?_⟩
  exact ⟨canonicalQueueBoundary
      (interpret (cacheAsyncFrfFailureBudget cache async frf)),
    rfl, rfl, rfl, rfl⟩

theorem cache_async_frf_budget_yields_geometric_rate_certificate
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (frf : FrfWitness) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate
        (cacheAsyncFrfFailureBudget cache async frf) ∧
      rate.initialBound =
        cacheAsyncFrfFailureBudget cache async frf + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨budgetGeometricRate
    (cacheAsyncFrfFailureBudget cache async frf),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate
      (cacheAsyncFrfFailureBudget cache async frf)).hRateLtOne
  · exact (budgetGeometricRate
      (cacheAsyncFrfFailureBudget cache async frf)).hInitialBoundPos

theorem cache_async_frf_semantic_morphism_continuous_ergodicity_lift
    {Ω : Type}
    {maxQueue : Nat}
    (cache : CacheColdPath)
    (async : AsyncDurabilityStep)
    (frf : FrfWitness)
    (interpret : Nat → Nat)
    (hInterpret :
      interpret (cacheAsyncFrfFailureBudget cache async frf) =
        cacheAsyncFrfFailureBudget cache async frf)
    (embedding : Gnosis.DiscreteSubLatticeEmbedding Ω maxQueue)
    (witness : Gnosis.GeometricErgodicWitness maxQueue)
    (hKernelMatch : witness.envelope.kernel = embedding.discreteKernel) :
    cache.traceFoldCold = cache.escCanonMiss ∧
    frf.raceMass = 3 ∧
    interpret (cacheAsyncFrfFailureBudget cache async frf) =
      cacheAsyncFrfFailureBudget cache async frf ∧
    embedding.continuousKernel.fosterDrift ∧
    0 < embedding.continuousKernel.driftGap ∧
    witness.rate.rateNumerator < witness.rate.rateDenominator := by
  have hLift :=
    Gnosis.continuous_ergodicity_lift embedding witness hKernelMatch
  exact ⟨cache.hTrace, frf.hRace, hInterpret,
    hLift.1, hLift.2.1, hLift.2.2⟩

end CacheAsyncFrfQueueKernelBridge
