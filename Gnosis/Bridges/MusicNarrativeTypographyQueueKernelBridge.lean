import Init
import Gnosis.GeometricErgodicity

/-!
# Music/Narrative/Typography Queue Kernel Bridge

Finite rhythm-perturbation, narrative-crossing, and typography-friction
witnesses for stale MCP rows.
-/

namespace MusicNarrativeTypographyQueueKernelBridge

structure MusicSetup where
  periodicLoad : Nat
  swingPerturbation : Nat
  totalSpace : Nat
  hSwing : 1 ≤ swingPerturbation
  hTotal : totalSpace = periodicLoad + swingPerturbation
deriving Repr

structure NarrativeSetup where
  narrativeCrossings : Nat
  hNarrative : 1 ≤ narrativeCrossings
deriving Repr

structure TypographySetup where
  characterOne : Nat
  characterTwo : Nat
  ligatureUnknot : Nat
  frictionSave : Nat
  hLigature : characterOne + characterTwo = ligatureUnknot + frictionSave
  hFriction : 1 ≤ frictionSave
deriving Repr

def musicNarrativeTypographyFailureBudget
    (music : MusicSetup)
    (narrative : NarrativeSetup)
    (typography : TypographySetup) : Nat :=
  music.swingPerturbation + narrative.narrativeCrossings + typography.frictionSave

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

theorem music_narrative_typography_budget_positive
    (music : MusicSetup)
    (narrative : NarrativeSetup)
    (typography : TypographySetup) :
    0 < musicNarrativeTypographyFailureBudget music narrative typography := by
  unfold musicNarrativeTypographyFailureBudget
  rw [Nat.add_assoc]
  exact Nat.lt_add_right
    (narrative.narrativeCrossings + typography.frictionSave)
    music.hSwing

theorem music_narrative_typography_budget_at_least_two
    (music : MusicSetup)
    (narrative : NarrativeSetup)
    (typography : TypographySetup) :
    2 ≤ musicNarrativeTypographyFailureBudget music narrative typography := by
  unfold musicNarrativeTypographyFailureBudget
  have hTwo :
      1 + 1 ≤ music.swingPerturbation + narrative.narrativeCrossings :=
    Nat.add_le_add music.hSwing narrative.hNarrative
  have hLift :
      music.swingPerturbation + narrative.narrativeCrossings ≤
        music.swingPerturbation + narrative.narrativeCrossings +
          typography.frictionSave :=
    Nat.le_add_right
      (music.swingPerturbation + narrative.narrativeCrossings)
      typography.frictionSave
  exact Nat.le_trans hTwo hLift

theorem music_narrative_typography_budget_yields_unit_queue_boundary
    (music : MusicSetup)
    (narrative : NarrativeSetup)
    (typography : TypographySetup) :
    0 < music.swingPerturbation ∧
    music.totalSpace = music.periodicLoad + music.swingPerturbation ∧
    0 < narrative.narrativeCrossings ∧
    typography.characterOne + typography.characterTwo =
      typography.ligatureUnknot + typography.frictionSave ∧
    0 < typography.frictionSave ∧
    0 < musicNarrativeTypographyFailureBudget music narrative typography ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate =
        musicNarrativeTypographyFailureBudget music narrative typography ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount
            (musicNarrativeTypographyFailureBudget music narrative typography))
          (musicNarrativeTypographyFailureBudget music narrative typography) := by
  exact ⟨music.hSwing, music.hTotal, narrative.hNarrative,
    typography.hLigature, typography.hFriction,
    music_narrative_typography_budget_positive music narrative typography,
    ⟨canonicalQueueBoundary
      (musicNarrativeTypographyFailureBudget music narrative typography),
      rfl, rfl, rfl, rfl⟩⟩

theorem music_narrative_typography_budget_yields_positive_topological_deficit
    (music : MusicSetup)
    (narrative : NarrativeSetup)
    (typography : TypographySetup) :
    0 < topologicalDeficit
      (musicNarrativeTypographyFailureBudget music narrative typography + 1) 1 := by
  unfold topologicalDeficit
  rw [Nat.add_sub_cancel]
  exact music_narrative_typography_budget_positive music narrative typography

theorem music_narrative_typography_budget_does_not_force_arrival_le_one
    (music : MusicSetup)
    (narrative : NarrativeSetup)
    (typography : TypographySetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate =
          musicNarrativeTypographyFailureBudget music narrative typography →
        boundary.serviceRate =
          quorumSize
            (replicaCount
              (musicNarrativeTypographyFailureBudget music narrative typography))
            (musicNarrativeTypographyFailureBudget music narrative typography) →
        boundary.arrivalRate ≤ 1) := by
  intro hAll
  let boundary :=
    canonicalQueueBoundary
      (musicNarrativeTypographyFailureBudget music narrative typography)
  have hArrival :
      musicNarrativeTypographyFailureBudget music narrative typography ≤ 1 :=
    hAll boundary rfl rfl
  have hTwo : 2 ≤ 1 :=
    Nat.le_trans
      (music_narrative_typography_budget_at_least_two music narrative typography)
      hArrival
  exact (Nat.not_succ_le_self 1) hTwo

theorem music_narrative_typography_budget_yields_geometric_rate_certificate
    (music : MusicSetup)
    (narrative : NarrativeSetup)
    (typography : TypographySetup) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate
        (musicNarrativeTypographyFailureBudget music narrative typography) ∧
      rate.initialBound =
        musicNarrativeTypographyFailureBudget music narrative typography + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨budgetGeometricRate
      (musicNarrativeTypographyFailureBudget music narrative typography),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate
      (musicNarrativeTypographyFailureBudget music narrative typography)).hRateLtOne
  · exact (budgetGeometricRate
      (musicNarrativeTypographyFailureBudget music narrative typography)).hInitialBoundPos

structure MusicNarrativeTypographyKernelLiftAdapter where
  music : MusicSetup
  narrative : NarrativeSetup
  typography : TypographySetup
  budget : Nat
  hBudgetEq :
    budget = musicNarrativeTypographyFailureBudget music narrative typography
deriving Repr

namespace MusicNarrativeTypographyKernelLiftAdapter

theorem budget_pos_from_source
    (adapter : MusicNarrativeTypographyKernelLiftAdapter) :
    0 < adapter.budget := by
  rw [adapter.hBudgetEq]
  exact music_narrative_typography_budget_positive
    adapter.music adapter.narrative adapter.typography

theorem music_narrative_typography_continuous_ergodicity_lift
    {Ω : Type}
    {maxQueue : Nat}
    (adapter : MusicNarrativeTypographyKernelLiftAdapter)
    (embedding : Gnosis.DiscreteSubLatticeEmbedding Ω maxQueue)
    (witness : Gnosis.GeometricErgodicWitness maxQueue)
    (hKernelMatch : witness.envelope.kernel = embedding.discreteKernel) :
    0 < adapter.budget ∧
    adapter.music.totalSpace =
      adapter.music.periodicLoad + adapter.music.swingPerturbation ∧
    adapter.typography.characterOne + adapter.typography.characterTwo =
      adapter.typography.ligatureUnknot + adapter.typography.frictionSave ∧
    embedding.continuousKernel.fosterDrift ∧
    0 < embedding.continuousKernel.driftGap ∧
    witness.rate.rateNumerator < witness.rate.rateDenominator := by
  have hLift :=
    Gnosis.continuous_ergodicity_lift embedding witness hKernelMatch
  exact ⟨adapter.budget_pos_from_source, adapter.music.hTotal,
    adapter.typography.hLigature, hLift.1, hLift.2.1, hLift.2.2⟩

end MusicNarrativeTypographyKernelLiftAdapter

end MusicNarrativeTypographyQueueKernelBridge
