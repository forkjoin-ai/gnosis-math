import BuleyeanMath.ImmigrationTopology
import BuleyeanMath.DiversityIsConcurrency
import BuleyeanMath.DiversityOptimality
import BuleyeanMath.DiversityUnwound
import BuleyeanMath.AmericanFrontier
import BuleyeanMath.CommunityDominance

open scoped BigOperators ENNReal

namespace BuleyeanMath

/-!
# Immigration as Diversity Growth (Simplified)

Closes the loop between static diversity optimality and dynamic growth.

The simplification: immigration is `composeKnots`, assimilation is
`wallingtonRotation`. The diversity theory proves diversity is optimal;
the knot theory proves untangling terminates. Immigration connects them:
`composeKnots` grows β₁ (diversity injection), `wallingtonRotation`
reduces the crossing overhead (assimilation), and the American Frontier
guarantees higher β₁ means less waste.

## The Reduction Chain

```
composeKnots          → β₁ increases       → deficit decreases (American Frontier)
wallingtonRotation    → crossings reach 0   → assimilation converges (free)
community context     → effective crossings ↓ → faster convergence (CommunityDominance)
greedyPolicy failure  → Hope Gap            → rejection deadlocks (UntanglingKnotTheory)
```

Every theorem composes existing results. Zero -- placeholder.
-/

-- ═══════════════════════════════════════════════════════════════════════
-- THM-IMMIGRATION-GROWS-CONCURRENCY
--
-- By DiversityIsConcurrency, immigration simultaneously grows
-- diversity and effective concurrency. New crossings from the immigrant
-- knot become new parallel computation channels after assimilation.
-- ═══════════════════════════════════════════════════════════════════════

/-- Immigration grows concurrency: β₁ = diversity = effective concurrency,
    and immigration strictly increases β₁. -/
theorem immigration_grows_concurrency
    (host : HostTopology) (imm : ImmigrantTopology) :
    diversityCount host.knot.beta1 = effectiveConcurrency host.knot.beta1 ∧
    diversityCount (postImmigrationPaths host imm) =
      effectiveConcurrency (postImmigrationPaths host imm) ∧
    effectiveConcurrency host.knot.beta1 <
      effectiveConcurrency (postImmigrationPaths host imm) := by
  refine ⟨?_, ?_, ?_⟩
  · exact diversity_is_concurrency host.knot.beta1
  · exact diversity_is_concurrency (postImmigrationPaths host imm)
  · unfold effectiveConcurrency postImmigrationPaths
    omega

-- ═══════════════════════════════════════════════════════════════════════
-- THM-IMMIGRATION-CLOSES-DEFICIT
--
-- When the host operates below its intrinsic β₁*, immigration narrows
-- the gap. Sufficient immigration reaches zero deficit.
-- ═══════════════════════════════════════════════════════════════════════

/-- Immigration closes the deficit gap toward intrinsic β₁*. -/
theorem immigration_closes_deficit
    {intrinsicBeta : ℕ}
    (host : HostTopology) (imm : ImmigrantTopology)
    (hBelow : host.knot.beta1 < intrinsicBeta)
    (hStream : 1 ≤ host.knot.beta1) :
    topologicalDeficit intrinsicBeta (postImmigrationPaths host imm) ≤
      topologicalDeficit intrinsicBeta host.knot.beta1 := by
  apply deficit_monotone_in_streams
  · unfold postImmigrationPaths; omega
  · exact hStream

/-- Sufficient immigration fully closes the deficit. -/
theorem immigration_closes_deficit_fully
    {intrinsicBeta : ℕ}
    (host : HostTopology) (imm : ImmigrantTopology)
    (hIntrinsicPos : 1 ≤ intrinsicBeta)
    (hEnough : intrinsicBeta ≤ postImmigrationPaths host imm) :
    topologicalDeficit intrinsicBeta (postImmigrationPaths host imm) = 0 := by
  unfold topologicalDeficit computationBeta1 transportBeta1
  omega

-- ═══════════════════════════════════════════════════════════════════════
-- THM-SUCCESSIVE-IMMIGRATION-MONOTONE
--
-- Each wave starts from higher β₁. Successive waves are monotonically
-- improving. Community context from prior waves reduces integration cost.
-- ═══════════════════════════════════════════════════════════════════════

/-- Two successive immigration waves. -/
structure SuccessiveWaves where
  host : HostTopology
  wave1 : ImmigrantTopology
  wave2 : ImmigrantTopology

/-- β₁ after wave 1. -/
def SuccessiveWaves.beta1AfterWave1 (sw : SuccessiveWaves) : ℕ :=
  postImmigrationPaths sw.host sw.wave1

/-- β₁ after wave 2. -/
def SuccessiveWaves.beta1AfterWave2 (sw : SuccessiveWaves) : ℕ :=
  sw.beta1AfterWave1 + sw.wave2.knot.beta1

/-- Successive immigration is monotonically increasing in β₁. -/
theorem successive_immigration_monotone (sw : SuccessiveWaves) :
    sw.host.knot.beta1 < sw.beta1AfterWave1 ∧
    sw.beta1AfterWave1 < sw.beta1AfterWave2 := by
  constructor
  · unfold SuccessiveWaves.beta1AfterWave1 postImmigrationPaths; omega
  · unfold SuccessiveWaves.beta1AfterWave2; omega

/-- Successive immigration is monotonically decreasing in deficit. -/
theorem successive_immigration_deficit_monotone
    {intrinsicBeta : ℕ}
    (sw : SuccessiveWaves)
    (hStream : 1 ≤ sw.host.knot.beta1) :
    topologicalDeficit intrinsicBeta sw.beta1AfterWave2 ≤
      topologicalDeficit intrinsicBeta sw.beta1AfterWave1 ∧
    topologicalDeficit intrinsicBeta sw.beta1AfterWave1 ≤
      topologicalDeficit intrinsicBeta sw.host.knot.beta1 := by
  constructor
  · apply deficit_monotone_in_streams
    · unfold SuccessiveWaves.beta1AfterWave2; omega
    · unfold SuccessiveWaves.beta1AfterWave1 postImmigrationPaths; omega
  · apply deficit_monotone_in_streams
    · unfold SuccessiveWaves.beta1AfterWave1 postImmigrationPaths; omega
    · exact hStream

-- ═══════════════════════════════════════════════════════════════════════
-- THM-IMMIGRATION-BASIN-EXPANSION
--
-- Each genuinely new immigrant language expands the Forest's attractor
-- space. N languages → N basins. Immigration creates new fixed points.
-- ═══════════════════════════════════════════════════════════════════════

/-- Immigration expands the Forest's attractor space. -/
theorem immigration_basin_expansion
    (op1 : TranslateRaceOperator) (op2 : TranslateRaceOperator)
    (hGrowth : op1.numLanguages < op2.numLanguages) :
    op1.numLanguages < op2.numLanguages ∧
    (∀ l : Fin op1.numLanguages, forestStep op1 l = l) ∧
    (∀ l : Fin op2.numLanguages, forestStep op2 l = l) := by
  exact ⟨hGrowth, basin_stability_strong op1, basin_stability_strong op2⟩

-- ═══════════════════════════════════════════════════════════════════════
-- THM-MONOCULTURE-FRAGILITY
--
-- Blocking immigration = freezing β₁ = permanent waste.
-- Closed borders are thermodynamically expensive.
-- ═══════════════════════════════════════════════════════════════════════

/-- Monoculture has permanent positive deficit. -/
theorem monoculture_permanent_deficit
    {intrinsicBeta : ℕ}
    (hBeta : 2 ≤ intrinsicBeta) :
    0 < topologicalDeficit intrinsicBeta 1 :=
  (deficit_information_loss hBeta).1

/-- Blocking immigration preserves permanent waste. A single immigration
    event would reduce it. -/
theorem blocked_immigration_permanent_waste
    {intrinsicBeta : ℕ}
    (host : HostTopology)
    (hBelow : host.knot.beta1 < intrinsicBeta)
    (hBeta : 2 ≤ intrinsicBeta)
    (hStream : 1 ≤ host.knot.beta1) :
    0 < topologicalDeficit intrinsicBeta host.knot.beta1 ∧
    topologicalDeficit intrinsicBeta (host.knot.beta1 + 1) ≤
      topologicalDeficit intrinsicBeta host.knot.beta1 := by
  constructor
  · unfold topologicalDeficit computationBeta1 transportBeta1; omega
  · apply deficit_monotone_in_streams (by omega) hStream

-- ═══════════════════════════════════════════════════════════════════════
-- THM-IMMIGRATION-DIVERSITY-INTEGRATION (master)
-- ═══════════════════════════════════════════════════════════════════════

/-- **THM-IMMIGRATION-DIVERSITY-INTEGRATION**: The complete integration.

    Immigration = composeKnots = diversity growth.
    Assimilation = wallingtonRotation = convergence.
    Community = prior context = acceleration.
    Rejection = permanent waste = thermodynamic trap. -/
theorem immigration_diversity_integration
    (host : HostTopology) (imm : ImmigrantTopology)
    (hNovel : 2 ≤ imm.knot.crossingNumber)
    (hMismatch : host.integrationStreams < imm.knot.crossingNumber)
    (communityContext : ℕ)
    (hCommunity : 0 < communityContext)
    {intrinsicBeta : ℕ}
    (hBelow : host.knot.beta1 < intrinsicBeta)
    (hBeta : 2 ≤ intrinsicBeta)
    (hStream : 1 ≤ host.knot.beta1) :
    -- Knot bridge: crossings add under connected sum
    (postImmigrationKnot host imm).crossingNumber =
      host.knot.crossingNumber + imm.knot.crossingNumber ∧
    -- Knot bridge: assimilation terminates
    (assimilate imm).crossingNumber = 0 ∧
    -- Growth: β₁ and concurrency increase
    host.knot.beta1 < (postImmigrationKnot host imm).beta1 ∧
    effectiveConcurrency host.knot.beta1 <
      effectiveConcurrency (postImmigrationPaths host imm) ∧
    -- Frontier: deficit decreases, zero at match
    topologicalDeficit intrinsicBeta (postImmigrationPaths host imm) ≤
      topologicalDeficit intrinsicBeta host.knot.beta1 ∧
    topologicalDeficit (postImmigrationPaths host imm)
      (postImmigrationPaths host imm) = 0 ∧
    -- Convergence: assimilation → 0 under dialogue
    (∀ c1 c2 : ℕ, c1 ≤ c2 →
      assimilationDeficit host imm hNovel c2 ≤
        assimilationDeficit host imm hNovel c1) ∧
    -- Community: accelerates integration
    communityReducedDeficit (immigrationFailureTopology host imm hNovel)
      communityContext ≤
      schedulingDeficit (immigrationFailureTopology host imm hNovel) ∧
    -- Rejection: deadlock + permanent waste
    ¬ greedyPolicy host.knot.crossingNumber
      (postImmigrationKnot host imm).crossingNumber ∧
    0 < topologicalDeficit intrinsicBeta host.knot.beta1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact immigration_is_connected_sum host imm
  · exact assimilation_terminates imm
  · exact immigration_increases_beta1 host imm
  · exact (immigration_grows_concurrency host imm).2.2
  · exact immigration_closes_deficit host imm hBelow hStream
  · exact immigration_zero_deficit_at_match host imm
  · exact fun c1 c2 h => assimilation_monotone_decreasing host imm hNovel c1 c2 h
  · exact community_accelerates_integration host imm hNovel communityContext hCommunity
  · exact greedy_rejection_deadlocks host imm
  · unfold topologicalDeficit computationBeta1 transportBeta1; omega

end BuleyeanMath
