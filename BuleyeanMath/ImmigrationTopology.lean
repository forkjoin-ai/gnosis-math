import BuleyeanMath.AmericanFrontier
import BuleyeanMath.CommunityDominance
import BuleyeanMath.DeficitCapacity
import BuleyeanMath.DiversityIsConcurrency
import BuleyeanMath.DiversityOptimality
import BuleyeanMath.SemioticDeficit
import BuleyeanMath.SemioticPeace
import BuleyeanMath.UntanglingKnotTheory

open scoped BigOperators ENNReal

namespace BuleyeanMath

/-!
# Immigration Topology (Simplified)

Immigration is knot connected sum: splicing a foreign topology into a host.

The key reduction: `postImmigrationPaths` is `composeKnots` on the path count,
and assimilation is `wallingtonRotation` on the composed knot. The Wallington
Rotation already proves termination and invariant preservation, so immigration
convergence is a free corollary — not a separate theory.

## The Knot-Theoretic Bridge

| Immigration concept | Knot concept | Existing theorem |
|---|---|---|
| Host topology | Knot A | `AlgorithmicKnot` |
| Immigrant topology | Knot B | `AlgorithmicKnot` |
| Post-immigration | Connected sum A#B | `composeKnots` |
| Assimilation | Untangling A#B | `wallingtonRotation` |
| Convergence | Termination | `wallington_produces_unknot` |
| Invariant preservation | I/O preserved | `wallington_preserves_invariant` |
| Greedy deadlock | Hope Gap | `¬ greedyPolicy` on the spike |
| Arrival deficit | Crossing number of B | `composition_crossings` |

This module proves:

1. **THM-IMMIGRATION-is-CONNECTED-SUM**: Immigration is `composeKnots` —
   crossings add, invariants compose, β₁ sums.

2. **THM-ASSIMILATION-is-WALLINGTON**: Assimilation is `wallingtonRotation`
   on the immigrant's crossings — it terminates, preserves invariants, and
   reaches the unknot.

3. **THM-IMMIGRATION-DIVERSITY-INJECTION**: Non-redundant immigrant paths
   strictly increase host β₁ and reduce waste on the American Frontier.

4. **THM-SEMIOTIC-DEFICIT-AT-ARRIVAL**: The crossing number of the immigrant
   knot is the semiotic deficit at arrival — real structure the host can't
   yet read.

5. **THM-GREEDY-REJECTION-DEADLOCKS**: A policy that rejects all crossing
   increases cannot untangle — the Hope Gap applied to immigration.

6. **THM-XENOPHOBIC-PHANTOM-COST**: Maintaining a phantom ("foreign crossings
   are fake") costs more per round than one-time integration.

7. **THM-COMMUNITY-ACCELERATES-INTEGRATION**: Prior diversity reduces the
   immigrant's effective crossing number (community context is pre-untangling).

8. **THM-IMMIGRATION-TOPOLOGY (master)**: The complete conjunction.

Every theorem is -- placeholder-free. The simplification reduces the immigration surface
from a standalone theory to a reading of `composeKnots` + `wallingtonRotation`
through the semiotic deficit / community dominance lens.
-/

-- ═══════════════════════════════════════════════════════════════════════
-- Structures (simplified: thin wrappers over AlgorithmicKnot)
-- ═══════════════════════════════════════════════════════════════════════

/-- An immigrant topology as an algorithmic knot: the structural crossings
    carried from the origin system. novelCrossings = crossings that don't
    exist in the host (non-redundant structure). The invariant captures
    the immigrant's I/O behavior signature. -/
structure ImmigrantTopology where
  /-- The immigrant's knot: crossings, invariant, β₁ -/
  knot : AlgorithmicKnot
  /-- At least one novel crossing (non-trivial immigration) -/
  hNovelPos : 0 < knot.crossingNumber

/-- Convenience: novel path count = crossing number of the immigrant knot. -/
def ImmigrantTopology.novelPaths (imm : ImmigrantTopology) : ℕ :=
  imm.knot.crossingNumber

/-- A host topology as an algorithmic knot: the existing community structure. -/
structure HostTopology where
  /-- The host's knot: crossings, invariant, β₁ -/
  knot : AlgorithmicKnot
  /-- Integration channels (articulation streams) -/
  integrationStreams : ℕ
  /-- At least two existing paths (nontrivial host) -/
  hHostPos : 2 ≤ knot.beta1
  /-- At least one integration channel -/
  hIntegrationPos : 0 < integrationStreams

-- ═══════════════════════════════════════════════════════════════════════
-- THM-IMMIGRATION-is-CONNECTED-SUM
--
-- Immigration is composeKnots. Crossings add, invariants compose, β₁ sums.
-- This is the foundational reduction: every immigration theorem is a
-- corollary of knot connected sum + Wallington Rotation.
-- ═══════════════════════════════════════════════════════════════════════

/-- The post-immigration knot: connected sum of host and immigrant. -/
def postImmigrationKnot (host : HostTopology) (imm : ImmigrantTopology) :
    AlgorithmicKnot :=
  composeKnots host.knot imm.knot

/-- Post-immigration crossing count = host crossings + immigrant crossings. -/
theorem immigration_is_connected_sum (host : HostTopology) (imm : ImmigrantTopology) :
    (postImmigrationKnot host imm).crossingNumber =
      host.knot.crossingNumber + imm.knot.crossingNumber :=
  composition_crossings host.knot imm.knot

/-- Post-immigration β₁ = host β₁ + immigrant β₁. -/
theorem immigration_beta1_additive (host : HostTopology) (imm : ImmigrantTopology) :
    (postImmigrationKnot host imm).beta1 =
      host.knot.beta1 + imm.knot.beta1 := by
  rfl

/-- Immigration strictly increases β₁. -/
theorem immigration_increases_beta1 (host : HostTopology) (imm : ImmigrantTopology) :
    host.knot.beta1 < (postImmigrationKnot host imm).beta1 := by
  simp [postImmigrationKnot, composeKnots]
  omega

/-- Immigration strictly increases crossing number. -/
theorem immigration_increases_crossings (host : HostTopology) (imm : ImmigrantTopology) :
    host.knot.crossingNumber < (postImmigrationKnot host imm).crossingNumber := by
  simp [postImmigrationKnot, composeKnots]
  omega

-- ═══════════════════════════════════════════════════════════════════════
-- THM-ASSIMILATION-is-WALLINGTON
--
-- Assimilation is wallingtonRotation applied to the immigrant's crossings.
-- The Wallington Rotation already proves:
--   1. Termination (crossing number is a decreasing natural number)
--   2. Invariant preservation (I/O behavior unchanged)
--   3. Unknot production (crossings reach zero)
--
-- Therefore: assimilation terminates, preserves the immigrant's
-- contribution, and reaches zero unreadable crossings.
-- ═══════════════════════════════════════════════════════════════════════

/-- Assimilate the immigrant's crossings via Wallington Rotation.
    Returns the untangled knot with zero crossings and preserved invariant. -/
def assimilate (imm : ImmigrantTopology) : AlgorithmicKnot :=
  wallingtonRotation imm.knot

/-- Assimilation terminates at zero crossings. -/
theorem assimilation_terminates (imm : ImmigrantTopology) :
    (assimilate imm).crossingNumber = 0 :=
  wallington_produces_unknot imm.knot

/-- Assimilation preserves the immigrant's invariant (I/O behavior). -/
theorem assimilation_preserves_invariant (imm : ImmigrantTopology) :
    (assimilate imm).invariant = imm.knot.invariant :=
  wallington_preserves_invariant imm.knot

/-- After assimilation, the composed knot's immigrant crossings are gone. -/
theorem post_assimilation_crossings (host : HostTopology) (imm : ImmigrantTopology) :
    (composeKnots host.knot (assimilate imm)).crossingNumber =
      host.knot.crossingNumber := by
  simp [composeKnots, assimilation_terminates]

-- ═══════════════════════════════════════════════════════════════════════
-- THM-IMMIGRATION-DIVERSITY-INJECTION (via American Frontier)
--
-- Non-redundant immigrant paths strictly increase host β₁,
-- which by the American Frontier strictly reduces system waste.
-- ═══════════════════════════════════════════════════════════════════════

/-- Post-immigration β₁ for the deficit calculation. Uses β₁ as path count. -/
def postImmigrationPaths (host : HostTopology) (imm : ImmigrantTopology) : ℕ :=
  host.knot.beta1 + imm.knot.beta1

/-- Post-immigration deficit at matched diversity is zero. -/
theorem immigration_zero_deficit_at_match
    (host : HostTopology) (imm : ImmigrantTopology) :
    topologicalDeficit (postImmigrationPaths host imm)
      (postImmigrationPaths host imm) = 0 := by
  exact deficit_zero_at_match (by unfold postImmigrationPaths; omega)

/-- Immigration reduces topological deficit on the American Frontier. -/
theorem immigration_reduces_deficit
    (host : HostTopology) (imm : ImmigrantTopology)
    (hStream : 1 ≤ host.knot.beta1) :
    topologicalDeficit (postImmigrationPaths host imm)
      (postImmigrationPaths host imm) ≤
    topologicalDeficit (postImmigrationPaths host imm) host.knot.beta1 := by
  apply deficit_monotone_in_streams
  · unfold postImmigrationPaths; omega
  · exact hStream

-- ═══════════════════════════════════════════════════════════════════════
-- THM-SEMIOTIC-DEFICIT-AT-ARRIVAL
--
-- The immigrant's crossing number formalizes the semiotic deficit at arrival.
-- Real structure the host can't yet parse.
-- ═══════════════════════════════════════════════════════════════════════

/-- The semiotic channel at the immigration boundary. -/
def immigrationChannel (host : HostTopology) (imm : ImmigrantTopology)
    (hNovel : 2 ≤ imm.knot.crossingNumber) : SemioticChannel where
  semanticPaths := imm.knot.crossingNumber
  articulationStreams := host.integrationStreams
  contextPaths := 0
  hSemanticPos := hNovel
  hArticulationPos := host.hIntegrationPos
  hContextNonneg := trivial

/-- Positive deficit at arrival when crossings exceed integration channels. -/
theorem semiotic_deficit_at_arrival
    (host : HostTopology) (imm : ImmigrantTopology)
    (hNovel : 2 ≤ imm.knot.crossingNumber)
    (hMismatch : host.integrationStreams < imm.knot.crossingNumber) :
    0 < semioticDeficit (immigrationChannel host imm hNovel) :=
  semiotic_deficit (immigrationChannel host imm hNovel) hMismatch

-- ═══════════════════════════════════════════════════════════════════════
-- THM-ASSIMILATION-CONVERGENCE (via Community Dominance)
--
-- Community CRDT convergence applied to immigration. Each dialogue round
-- reduces the Bule deficit. This is the semiotic view of what the
-- Wallington Rotation does: each Reidemeister move = one dialogue round
-- = one Bule of integration.
-- ═══════════════════════════════════════════════════════════════════════

/-- The immigration failure topology for community dominance composition. -/
def immigrationFailureTopology (host : HostTopology)
    (imm : ImmigrantTopology) (hNovel : 2 ≤ imm.knot.crossingNumber) :
    FailureTopology where
  failurePaths := imm.knot.crossingNumber
  decisionStreams := host.integrationStreams
  hFailurePos := hNovel
  hDecisionPos := host.hIntegrationPos

/-- Assimilation deficit after c rounds of dialogue. -/
def assimilationDeficit (host : HostTopology) (imm : ImmigrantTopology)
    (hNovel : 2 ≤ imm.knot.crossingNumber) (dialogueRounds : ℕ) : ℤ :=
  buleDeficit (immigrationFailureTopology host imm hNovel) dialogueRounds

/-- Assimilation deficit decreases monotonically with dialogue.
    Each Reidemeister move on the immigrant knot = one dialogue round. -/
theorem assimilation_monotone_decreasing
    (host : HostTopology) (imm : ImmigrantTopology)
    (hNovel : 2 ≤ imm.knot.crossingNumber)
    (c1 c2 : ℕ) (hMore : c1 ≤ c2) :
    assimilationDeficit host imm hNovel c2 ≤
      assimilationDeficit host imm hNovel c1 :=
  bule_deficit_monotone_decreasing
    (immigrationFailureTopology host imm hNovel) c1 c2 hMore

/-- Sufficient dialogue eliminates the deficit. The bound is the immigrant's
    crossing number minus the host's integration streams — exactly the
    number of Reidemeister moves needed. -/
theorem assimilation_convergence
    (host : HostTopology) (imm : ImmigrantTopology)
    (hNovel : 2 ≤ imm.knot.crossingNumber)
    (dialogueRounds : ℕ)
    (hEnough : imm.knot.crossingNumber ≤ host.integrationStreams + dialogueRounds) :
    assimilationDeficit host imm hNovel dialogueRounds = 0 :=
  bule_convergence
    (immigrationFailureTopology host imm hNovel) dialogueRounds hEnough

-- ═══════════════════════════════════════════════════════════════════════
-- THM-GREEDY-REJECTION-DEADLOCKS
--
-- The Hope Gap applied to immigration: a policy that rejects all
-- crossing increases cannot perform composeKnots, and therefore cannot
-- integrate any non-trivial immigrant topology.
-- ═══════════════════════════════════════════════════════════════════════

/-- A greedy policy rejects all crossing increases. -/
def greedyPolicy (currentCrossings : ℕ) (proposedCrossings : ℕ) : Prop :=
  proposedCrossings ≤ currentCrossings

/-- Greedy rejection deadlocks immigration: composeKnots always increases
    crossings when the immigrant has positive crossings. The greedy
    policy therefore rejects every non-trivial immigration. -/
theorem greedy_rejection_deadlocks
    (host : HostTopology) (imm : ImmigrantTopology) :
    ¬ greedyPolicy host.knot.crossingNumber
      (postImmigrationKnot host imm).crossingNumber := by
  unfold greedyPolicy postImmigrationKnot composeKnots
  omega

-- ═══════════════════════════════════════════════════════════════════════
-- THM-XENOPHOBIC-PHANTOM-COST
--
-- Maintaining a phantom ("foreign crossings are fake") re-incurs the
-- full deficit every round. Integration pays it once and converges.
-- ═══════════════════════════════════════════════════════════════════════

/-- One-time integration cost = initial semiotic deficit. -/
def integrationCost (host : HostTopology) (imm : ImmigrantTopology)
    (hNovel : 2 ≤ imm.knot.crossingNumber)
    (hMismatch : host.integrationStreams < imm.knot.crossingNumber) : ℤ :=
  semioticDeficit (immigrationChannel host imm hNovel)

/-- Cumulative phantom cost = rounds × deficit (never converges). -/
def phantomMaintenanceCost (host : HostTopology) (imm : ImmigrantTopology)
    (hNovel : 2 ≤ imm.knot.crossingNumber)
    (hMismatch : host.integrationStreams < imm.knot.crossingNumber)
    (rounds : ℕ) : ℤ :=
  rounds * semioticDeficit (immigrationChannel host imm hNovel)

/-- Phantom cost exceeds integration cost after round 1. -/
theorem xenophobic_phantom_exceeds_integration
    (host : HostTopology) (imm : ImmigrantTopology)
    (hNovel : 2 ≤ imm.knot.crossingNumber)
    (hMismatch : host.integrationStreams < imm.knot.crossingNumber)
    (rounds : ℕ) (hRounds : 2 ≤ rounds) :
    integrationCost host imm hNovel hMismatch <
      phantomMaintenanceCost host imm hNovel hMismatch rounds := by
  unfold integrationCost phantomMaintenanceCost
  have hDefPos : 0 < semioticDeficit (immigrationChannel host imm hNovel) :=
    semiotic_deficit (immigrationChannel host imm hNovel) hMismatch
  nlinarith

-- ═══════════════════════════════════════════════════════════════════════
-- THM-COMMUNITY-ACCELERATES-INTEGRATION
--
-- Prior community context (from earlier immigrants, CRDT-synced) reduces
-- the effective crossing number for subsequent immigrants.
-- ═══════════════════════════════════════════════════════════════════════

/-- Community context reduces immigration deficit. -/
theorem community_accelerates_integration
    (host : HostTopology) (imm : ImmigrantTopology)
    (hNovel : 2 ≤ imm.knot.crossingNumber)
    (communityContext : ℕ)
    (hCommunity : 0 < communityContext) :
    communityReducedDeficit (immigrationFailureTopology host imm hNovel)
      communityContext ≤
    schedulingDeficit (immigrationFailureTopology host imm hNovel) :=
  community_attenuates_failure
    (immigrationFailureTopology host imm hNovel) communityContext hCommunity

-- ═══════════════════════════════════════════════════════════════════════
-- THM-IMMIGRATION-TOPOLOGY (master)
--
-- The complete immigration topology theory as a single conjunction.
-- Now with the knot-theoretic bridge making the reduction explicit.
-- ═══════════════════════════════════════════════════════════════════════

/-- **THM-IMMIGRATION-TOPOLOGY**: The complete immigration topology theory.

    Immigration = composeKnots. Assimilation = wallingtonRotation.
    The knot-theoretic bridge makes every immigration theorem a
    corollary of connected sum + untangling. -/
theorem immigration_topology
    (host : HostTopology) (imm : ImmigrantTopology)
    (hNovel : 2 ≤ imm.knot.crossingNumber)
    (hMismatch : host.integrationStreams < imm.knot.crossingNumber)
    (communityContext : ℕ)
    (hCommunity : 0 < communityContext) :
    -- Connected sum: crossings add
    (postImmigrationKnot host imm).crossingNumber =
      host.knot.crossingNumber + imm.knot.crossingNumber ∧
    -- β₁ adds
    host.knot.beta1 < (postImmigrationKnot host imm).beta1 ∧
    -- Assimilation terminates at zero crossings
    (assimilate imm).crossingNumber = 0 ∧
    -- Assimilation preserves invariant
    (assimilate imm).invariant = imm.knot.invariant ∧
    -- Positive deficit at arrival
    0 < semioticDeficit (immigrationChannel host imm hNovel) ∧
    -- Assimilation deficit monotonically decreasing
    (∀ c1 c2 : ℕ, c1 ≤ c2 →
      assimilationDeficit host imm hNovel c2 ≤
        assimilationDeficit host imm hNovel c1) ∧
    -- Greedy rejection deadlocks
    ¬ greedyPolicy host.knot.crossingNumber
      (postImmigrationKnot host imm).crossingNumber ∧
    -- Phantom cost exceeds integration cost
    integrationCost host imm hNovel hMismatch <
      phantomMaintenanceCost host imm hNovel hMismatch 2 ∧
    -- Community accelerates integration
    communityReducedDeficit (immigrationFailureTopology host imm hNovel)
      communityContext ≤
      schedulingDeficit (immigrationFailureTopology host imm hNovel) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact immigration_is_connected_sum host imm
  · exact immigration_increases_beta1 host imm
  · exact assimilation_terminates imm
  · exact assimilation_preserves_invariant imm
  · exact semiotic_deficit_at_arrival host imm hNovel hMismatch
  · exact fun c1 c2 h => assimilation_monotone_decreasing host imm hNovel c1 c2 h
  · exact greedy_rejection_deadlocks host imm
  · exact xenophobic_phantom_exceeds_integration host imm hNovel hMismatch 2 (by omega)
  · exact community_accelerates_integration host imm hNovel communityContext hCommunity

end BuleyeanMath
