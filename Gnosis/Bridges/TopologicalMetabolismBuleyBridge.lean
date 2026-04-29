import Gnosis.TopologicalMetabolism
import Gnosis.BuleySelfSimilarityViolation
import Gnosis.BuleyTransformerSSMBridge

/-!
# Topological Metabolism ↔ Buley Runtime Bridge

This module connects the `TopologicalMetabolism.RuntimeGovernance`
pre-collapse ladder back to the existing Bule self-similarity remediation
surface. The bridge is intentionally finite: a saturated brown fingerprint
projects to a Bule unit whose score is exactly one contract over the
two-head attention / Hexon manifold ceiling.

Imports only existing Init-only Gnosis modules and no Mathlib.
-/

namespace Gnosis
namespace TopologicalMetabolismBuleyBridge

open Gnosis.SpectralNoiseEquilibrium
open Gnosis.RuntimeGovernance
open Gnosis.BuleySelfSimilarityViolation
open Gnosis.BuleyTransformerSSMBridge

/-! ## Fingerprint pressure as Bule pressure -/

/-- Runtime fingerprint pressure as a Bule unit:
low-band mass maps to waste, high-band mass to opportunity, and spectral
slope magnitude to diversity. This is the proof-facing mirror of the
TypeScript `fingerprintBuleyProjection` helper. -/
def fingerprintBuleyUnit (fp : SpectralFingerprint) : BuleyUnit :=
  ⟨fp.lowBand, fp.highBand, fp.slopeMagnitude⟩

def observationBuleyUnit (o : MeshObservation) : BuleyUnit :=
  fingerprintBuleyUnit o.fingerprint

/-- The runtime governance bridge uses the two-head attention ceiling,
which is the Hexon tower ceiling. -/
def twoHeadHexonCeiling : ManifoldPhaseCount :=
  multiHeadPhaseCount 2

theorem two_head_hexon_ceiling_is_six :
    twoHeadHexonCeiling = 6 := by
  unfold twoHeadHexonCeiling multiHeadPhaseCount
  decide

theorem two_head_attention_ceiling_matches_tower_hexon :
    twoHeadHexonCeiling = Gnosis.BraidedTower.towerPhaseCount [3, 2] := by
  unfold twoHeadHexonCeiling multiHeadPhaseCount
  decide

theorem pink_normal_fingerprint_score_is_four :
    buleyUnitScore (observationBuleyUnit pinkNormalObservation) = 4 := by
  unfold observationBuleyUnit fingerprintBuleyUnit pinkNormalObservation
    colorFingerprint buleyUnitScore
  decide

theorem brown_pre_collapse_fingerprint_score_is_seven :
    buleyUnitScore (observationBuleyUnit brownPreCollapseObservation) = 7 := by
  unfold observationBuleyUnit fingerprintBuleyUnit brownPreCollapseObservation
    colorFingerprint buleyUnitScore
  decide

theorem pink_normal_inside_two_head_attention_ceiling :
    insideManifold (observationBuleyUnit pinkNormalObservation)
      twoHeadHexonCeiling := by
  unfold insideManifold
  rw [pink_normal_fingerprint_score_is_four, two_head_hexon_ceiling_is_six]
  decide

theorem pink_normal_has_no_bule_violation :
    ¬ selfSimilarityViolation
      (observationBuleyUnit pinkNormalObservation)
      twoHeadHexonCeiling := by
  unfold selfSimilarityViolation
  rw [pink_normal_fingerprint_score_is_four, two_head_hexon_ceiling_is_six]
  decide

theorem brown_pre_collapse_exceeds_two_head_attention_ceiling :
    selfSimilarityViolation
      (observationBuleyUnit brownPreCollapseObservation)
      twoHeadHexonCeiling := by
  unfold selfSimilarityViolation
  rw [brown_pre_collapse_fingerprint_score_is_seven,
    two_head_hexon_ceiling_is_six]
  decide

theorem brown_pre_collapse_contract_debt_is_one :
    correctiveContractCount
      (observationBuleyUnit brownPreCollapseObservation)
      twoHeadHexonCeiling = 1 := by
  unfold correctiveContractCount
  rw [brown_pre_collapse_fingerprint_score_is_seven,
    two_head_hexon_ceiling_is_six]

theorem brown_pre_collapse_remediates_to_two_head_ceiling :
    buleyUnitScore (observationBuleyUnit brownPreCollapseObservation)
      - correctiveContractCount
        (observationBuleyUnit brownPreCollapseObservation)
        twoHeadHexonCeiling
        = twoHeadHexonCeiling := by
  exact remediated_score_equals_ceiling
    brown_pre_collapse_exceeds_two_head_attention_ceiling

/-! ## Re-shard recommendation as Bule remediation -/

def reshardBulePressure (o : MeshObservation)
    (ceiling : ManifoldPhaseCount) : Prop :=
  reshardRecommended o ∧
    selfSimilarityViolation (observationBuleyUnit o) ceiling

theorem brown_pre_collapse_reshard_is_bule_pressure :
    reshardBulePressure brownPreCollapseObservation twoHeadHexonCeiling := by
  exact ⟨brown_pre_collapse_recommends_reshard,
    brown_pre_collapse_exceeds_two_head_attention_ceiling⟩

theorem brown_pre_collapse_reshard_has_positive_bule_debt :
    reshardRecommended brownPreCollapseObservation →
      0 < correctiveContractCount
        (observationBuleyUnit brownPreCollapseObservation)
        twoHeadHexonCeiling := by
  intro _
  rw [brown_pre_collapse_contract_debt_is_one]
  decide

theorem collapsed_observation_remains_recovery_not_reshard :
    boundaryCollapsed brownCollapsedObservation
      ∧ ¬ reshardRecommended brownCollapsedObservation := by
  constructor
  · exact collapsed_observation_is_hard_collapse
  · intro hReshard
    exact hReshard.2 collapsed_observation_is_hard_collapse

theorem runtime_governance_buley_bridge_bundle :
    ¬ selfSimilarityViolation
      (observationBuleyUnit pinkNormalObservation)
      twoHeadHexonCeiling
      ∧ selfSimilarityViolation
        (observationBuleyUnit brownPreCollapseObservation)
        twoHeadHexonCeiling
      ∧ correctiveContractCount
        (observationBuleyUnit brownPreCollapseObservation)
        twoHeadHexonCeiling = 1
      ∧ reshardRecommended brownPreCollapseObservation
      ∧ boundaryCollapsed brownCollapsedObservation
      ∧ twoHeadHexonCeiling = Gnosis.BraidedTower.towerPhaseCount [3, 2] := by
  exact ⟨pink_normal_has_no_bule_violation,
    brown_pre_collapse_exceeds_two_head_attention_ceiling,
    brown_pre_collapse_contract_debt_is_one,
    brown_pre_collapse_recommends_reshard,
    collapsed_observation_is_hard_collapse,
    two_head_attention_ceiling_matches_tower_hexon⟩

end TopologicalMetabolismBuleyBridge
end Gnosis
