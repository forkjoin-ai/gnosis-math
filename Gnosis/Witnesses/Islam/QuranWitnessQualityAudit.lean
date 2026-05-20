import Gnosis.Witnesses.Islam.QuranAlFatihaOpeningWitness
import Gnosis.Witnesses.Islam.QuranAlBaqaraGuidanceGroupsWitness
import Gnosis.Witnesses.Islam.QuranSubmissionTopologyWitness

namespace Gnosis.Witnesses.Islam
namespace QuranWitnessQualityAudit

/-!
# Quran Witness Quality Audit

The existing Islam surface compiles, but much of it was produced as literal
inventory before the later cultural-witness quality bar hardened. This module
records the salvage decision mechanically:

  * keep the source-order Quran modules because they are clean, bounded, and
    imported;
  * do not treat literal inventory as finished quality;
  * use the repaired opening modules as the upgrade pattern: invariant,
    gap/counterproof, and framework convergence;
  * continue Quran work by upgrading one coherent source boundary at a time.

No `sorry`, no new `axiom`.
-/

inductive IslamLeanStatus
  | compilesClean
  | literalInventoryDebt
  | frameworkBearing
  | upgradeInPlace
deriving DecidableEq, Repr

def islamQualityAudit : List IslamLeanStatus :=
  [ IslamLeanStatus.compilesClean
  , IslamLeanStatus.literalInventoryDebt
  , IslamLeanStatus.frameworkBearing
  , IslamLeanStatus.upgradeInPlace
  ]

structure IslamSalvageDecision where
  syntaxSalvageable : Bool := true
  literalInventoryNeedsUpgrade : Bool := true
  openingNowCarriesInvariantGap : Bool := true
  submissionTopologyCarriesFramework : Bool := true
  quarantineNotNeededForImportedSurface : Bool := true
deriving DecidableEq, Repr

def islamSalvageDecision : IslamSalvageDecision := {}

def salvageByUpgrade (d : IslamSalvageDecision) : Prop :=
  d.syntaxSalvageable = true ∧
  d.literalInventoryNeedsUpgrade = true ∧
  d.openingNowCarriesInvariantGap = true ∧
  d.submissionTopologyCarriesFramework = true ∧
  d.quarantineNotNeededForImportedSurface = true

theorem islam_salvage_by_upgrade :
    salvageByUpgrade islamSalvageDecision := by
  unfold salvageByUpgrade islamSalvageDecision
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem islam_quality_audit_shape :
    islamQualityAudit.length = 4
    ∧ islamQualityAudit.head? = some IslamLeanStatus.compilesClean
    ∧ islamQualityAudit.getLast? = some IslamLeanStatus.upgradeInPlace := by
  exact ⟨rfl, rfl, rfl⟩

theorem repaired_opening_modules_are_framework_bearing :
    QuranAlFatihaOpeningWitness.guidanceGapExcludesCollapse
      QuranAlFatihaOpeningWitness.worshipGuidancePattern ∧
    QuranAlBaqaraGuidanceGroupsWitness.negativeGroupsExposeGuidanceBoundary
      QuranAlBaqaraGuidanceGroupsWitness.sealedDisbelieverPattern
      QuranAlBaqaraGuidanceGroupsWitness.hypocritePattern ∧
    QuranSubmissionTopologyWitness.islamGroundPattern.zeroDeficit = true := by
  exact ⟨QuranAlFatihaOpeningWitness.al_fatiha_guidance_gap,
    QuranAlBaqaraGuidanceGroupsWitness.baqara_negative_groups_expose_boundary,
    rfl⟩

theorem quran_witness_quality_audit :
    salvageByUpgrade islamSalvageDecision ∧
    islamQualityAudit.length = 4 ∧
    QuranAlFatihaOpeningWitness.guidanceGapExcludesCollapse
      QuranAlFatihaOpeningWitness.worshipGuidancePattern ∧
    QuranAlBaqaraGuidanceGroupsWitness.baqaraGuidanceAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    QuranSubmissionTopologyWitness.islamGroundPattern.zeroDeficit = true := by
  exact ⟨islam_salvage_by_upgrade,
    islam_quality_audit_shape.left,
    QuranAlFatihaOpeningWitness.al_fatiha_guidance_gap,
    QuranAlBaqaraGuidanceGroupsWitness.baqara_guidance_access_archaeological,
    rfl⟩

end QuranWitnessQualityAudit
end Gnosis.Witnesses.Islam
