import Init
import Gnosis.GeometricErgodicity

/-!
# Ki/FRF/Training Queue Kernel Bridge

Finite Ki precursor-leak, fork/race/fold dominance, and training-witness
certificates for stale MCP rows.
-/

namespace KiFrfTrainingQueueKernelBridge

structure KiLeakWitness where
  glanceLeak : Nat
  muscleLeak : Nat
  scentLeak : Nat
  energyLeak : Nat
  hLeak :
    0 < glanceLeak ∨ 0 < muscleLeak ∨ 0 < scentLeak ∨ 0 < energyLeak
deriving Repr

def totalLeak (ki : KiLeakWitness) : Nat :=
  ki.glanceLeak + ki.muscleLeak + ki.scentLeak + ki.energyLeak

structure TimelineWitness where
  reactionTick : Nat
  actionTick : Nat
  hTimeline : reactionTick < actionTick
deriving Repr

structure FrfWitness where
  forkFutures : Nat
  foldAction : Nat
  raceScore : Nat
  hFork : 0 < forkFutures
  hDominates : foldAction ≤ raceScore
  hRacePositive : 0 < raceScore
deriving Repr

structure TrainingWitness where
  sampleSeriesBeats : Nat
  correctCount : Nat
  chanceBaseline : Nat
  hBeatsChance : chanceBaseline < correctCount
  hSamples : 0 < sampleSeriesBeats
deriving Repr

def kiFrfTrainingFailureBudget
    (ki : KiLeakWitness)
    (training : TrainingWitness)
    (frf : FrfWitness) : Nat :=
  totalLeak ki + training.correctCount + frf.raceScore

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

theorem total_leak_positive (ki : KiLeakWitness) :
    0 < totalLeak ki := by
  unfold totalLeak
  rcases ki.hLeak with hGlance | hMuscle | hScent | hEnergy
  · have hPair : 0 < ki.glanceLeak + ki.muscleLeak :=
      Nat.lt_add_right ki.muscleLeak hGlance
    have hTriple : 0 < ki.glanceLeak + ki.muscleLeak + ki.scentLeak :=
      Nat.lt_add_right ki.scentLeak hPair
    exact Nat.lt_add_right ki.energyLeak hTriple
  · have hPair : 0 < ki.glanceLeak + ki.muscleLeak :=
      Nat.lt_add_left ki.glanceLeak hMuscle
    have hTriple : 0 < ki.glanceLeak + ki.muscleLeak + ki.scentLeak :=
      Nat.lt_add_right ki.scentLeak hPair
    exact Nat.lt_add_right ki.energyLeak hTriple
  · have hTriple : 0 < ki.glanceLeak + ki.muscleLeak + ki.scentLeak :=
      Nat.lt_add_left (ki.glanceLeak + ki.muscleLeak) hScent
    exact Nat.lt_add_right ki.energyLeak hTriple
  · exact Nat.lt_add_left
      (ki.glanceLeak + ki.muscleLeak + ki.scentLeak)
      hEnergy

theorem training_correct_count_positive (training : TrainingWitness) :
    0 < training.correctCount :=
  Nat.lt_of_le_of_lt (Nat.zero_le training.chanceBaseline)
    training.hBeatsChance

theorem ki_frf_training_budget_positive
    (ki : KiLeakWitness)
    (training : TrainingWitness)
    (frf : FrfWitness) :
    0 < kiFrfTrainingFailureBudget ki training frf := by
  unfold kiFrfTrainingFailureBudget
  rw [Nat.add_assoc]
  exact Nat.lt_add_right
    (training.correctCount + frf.raceScore)
    (total_leak_positive ki)

theorem ki_frf_training_budget_yields_unit_queue_boundary
    (ki : KiLeakWitness)
    (timeline : TimelineWitness)
    (training : TrainingWitness)
    (frf : FrfWitness) :
    0 < totalLeak ki ∧
    timeline.reactionTick < timeline.actionTick ∧
    training.chanceBaseline < training.correctCount ∧
    0 < training.correctCount ∧
    frf.foldAction ≤ frf.raceScore ∧
    0 < frf.raceScore ∧
    0 < kiFrfTrainingFailureBudget ki training frf ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = kiFrfTrainingFailureBudget ki training frf ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (kiFrfTrainingFailureBudget ki training frf))
          (kiFrfTrainingFailureBudget ki training frf) := by
  exact ⟨total_leak_positive ki, timeline.hTimeline, training.hBeatsChance,
    training_correct_count_positive training, frf.hDominates, frf.hRacePositive,
    ki_frf_training_budget_positive ki training frf,
    ⟨canonicalQueueBoundary (kiFrfTrainingFailureBudget ki training frf),
      rfl, rfl, rfl, rfl⟩⟩

theorem ki_frf_training_budget_yields_positive_topological_deficit
    (ki : KiLeakWitness)
    (training : TrainingWitness)
    (frf : FrfWitness) :
    0 < topologicalDeficit
      (kiFrfTrainingFailureBudget ki training frf + 1) 1 := by
  unfold topologicalDeficit
  rw [Nat.add_sub_cancel]
  exact ki_frf_training_budget_positive ki training frf

theorem ki_frf_training_budget_does_not_force_beta1_equals_budget
    (ki : KiLeakWitness)
    (training : TrainingWitness)
    (frf : FrfWitness) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = kiFrfTrainingFailureBudget ki training frf →
        boundary.serviceRate =
          quorumSize
            (replicaCount (kiFrfTrainingFailureBudget ki training frf))
            (kiFrfTrainingFailureBudget ki training frf) →
        boundary.beta1 = kiFrfTrainingFailureBudget ki training frf) := by
  intro hAll
  let boundary := canonicalQueueBoundary (kiFrfTrainingFailureBudget ki training frf)
  have hEq : boundary.beta1 = kiFrfTrainingFailureBudget ki training frf :=
    hAll boundary rfl rfl
  have hPositive : 0 < kiFrfTrainingFailureBudget ki training frf :=
    ki_frf_training_budget_positive ki training frf
  rw [show boundary.beta1 = 0 by rfl] at hEq
  rw [← hEq] at hPositive
  exact Nat.lt_irrefl 0 hPositive

structure RetrialQueueKernelFamily where
  maxQueue : Nat
  maxOrbit : Nat
  stationaryBalance : Bool
  terminalBalance : Bool
deriving Repr

structure KiFrfTrainingRetrialAdapter where
  ki : KiLeakWitness
  timeline : TimelineWitness
  training : TrainingWitness
  frf : FrfWitness
  kernel : RetrialQueueKernelFamily
  budget : Nat
  hBudgetEq : budget = kiFrfTrainingFailureBudget ki training frf
deriving Repr

namespace KiFrfTrainingRetrialAdapter

theorem retrial_stationary_balance_bridge
    (adapter : KiFrfTrainingRetrialAdapter) :
    adapter.budget =
      kiFrfTrainingFailureBudget adapter.ki adapter.training adapter.frf ∧
    0 < adapter.budget ∧
    adapter.timeline.reactionTick < adapter.timeline.actionTick ∧
    adapter.training.chanceBaseline < adapter.training.correctCount ∧
    adapter.frf.foldAction ≤ adapter.frf.raceScore ∧
    adapter.kernel.stationaryBalance = adapter.kernel.stationaryBalance ∧
    adapter.kernel.terminalBalance = adapter.kernel.terminalBalance := by
  rw [adapter.hBudgetEq]
  exact ⟨rfl,
    ki_frf_training_budget_positive adapter.ki adapter.training adapter.frf,
    adapter.timeline.hTimeline,
    adapter.training.hBeatsChance,
    adapter.frf.hDominates,
    rfl,
    rfl⟩

end KiFrfTrainingRetrialAdapter

theorem ki_frf_training_budget_yields_geometric_rate_certificate
    (ki : KiLeakWitness)
    (training : TrainingWitness)
    (frf : FrfWitness) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (kiFrfTrainingFailureBudget ki training frf) ∧
      rate.initialBound = kiFrfTrainingFailureBudget ki training frf + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨budgetGeometricRate (kiFrfTrainingFailureBudget ki training frf),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate
      (kiFrfTrainingFailureBudget ki training frf)).hRateLtOne
  · exact (budgetGeometricRate
      (kiFrfTrainingFailureBudget ki training frf)).hInitialBoundPos

structure KiFrfTrainingKernelLiftAdapter where
  ki : KiLeakWitness
  timeline : TimelineWitness
  training : TrainingWitness
  frf : FrfWitness
  budget : Nat
  hBudgetEq : budget = kiFrfTrainingFailureBudget ki training frf
deriving Repr

namespace KiFrfTrainingKernelLiftAdapter

theorem budget_pos_from_source
    (adapter : KiFrfTrainingKernelLiftAdapter) :
    0 < adapter.budget := by
  rw [adapter.hBudgetEq]
  exact ki_frf_training_budget_positive
    adapter.ki adapter.training adapter.frf

theorem ki_frf_training_continuous_ergodicity_lift
    {Ω : Type}
    {maxQueue : Nat}
    (adapter : KiFrfTrainingKernelLiftAdapter)
    (embedding : Gnosis.DiscreteSubLatticeEmbedding Ω maxQueue)
    (witness : Gnosis.GeometricErgodicWitness maxQueue)
    (hKernelMatch : witness.envelope.kernel = embedding.discreteKernel) :
    0 < adapter.budget ∧
    adapter.timeline.reactionTick < adapter.timeline.actionTick ∧
    adapter.training.chanceBaseline < adapter.training.correctCount ∧
    adapter.frf.foldAction ≤ adapter.frf.raceScore ∧
    embedding.continuousKernel.fosterDrift ∧
    0 < embedding.continuousKernel.driftGap ∧
    witness.rate.rateNumerator < witness.rate.rateDenominator := by
  have hLift :=
    Gnosis.continuous_ergodicity_lift embedding witness hKernelMatch
  exact ⟨adapter.budget_pos_from_source, adapter.timeline.hTimeline,
    adapter.training.hBeatsChance, adapter.frf.hDominates,
    hLift.1, hLift.2.1, hLift.2.2⟩

end KiFrfTrainingKernelLiftAdapter

end KiFrfTrainingQueueKernelBridge
