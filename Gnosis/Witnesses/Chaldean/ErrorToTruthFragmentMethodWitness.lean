import Gnosis.Witnesses.Chaldean.ChaldeanGenesisFragmentRecoveryWitness
import Gnosis.Witnesses.Chaldean.ComparativeFloodMethodReserveWitness
import Gnosis.Witnesses.Chaldean.MummuTiamatuPleromaMattressWitness

namespace Gnosis.Witnesses.Chaldean
namespace ErrorToTruthFragmentMethodWitness

/-!
# Error-To-Truth Fragment Method Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, conclusion.

Smith's conclusion gives the native method for reading damaged Chaldean
sources. He marks his Nimrod/Izdubar chronology as hazardous, admits that it
rests on plausible but probably superficial grounds, and says new material would
change his views again. That does not make the witness unusable. It makes the
method honest: provisional theories can serve inquiry while being corrected by
new fragments. In cuneiform matters, he says, the path often advances through
error to truth.

This is the anti-overclaim theorem for the whole Chaldean grind. The fragment
graph may support structural topology before it supports name identity or
chronological certainty. Mythic material also has mixed value: some stories are
genuine traditions, some natural-phenomena explanations, some romances. The
method preserves all three labels instead of flattening them.

No `sorry`, no new `axiom`.
-/

structure HazardousTheoryReserve where
  nimrodChronologyMarkedHazardous : Bool := true
  plausibleGroundsAdmitted : Bool := true
  superficialGroundsPossible : Bool := true
  clueNeededForHeroPosition : Bool := true
  theoryHeldAsScaffoldNotClosure : Bool := true
deriving DecidableEq, Repr

def hazardousTheoryReserve : HazardousTheoryReserve := {}

def boundedHazardousTheory (h : HazardousTheoryReserve) : Prop :=
  h.nimrodChronologyMarkedHazardous = true ∧
  h.plausibleGroundsAdmitted = true ∧
  h.superficialGroundsPossible = true ∧
  h.clueNeededForHeroPosition = true ∧
  h.theoryHeldAsScaffoldNotClosure = true

structure FragmentCorrectionDiscipline where
  brokenFragmentsDifficult : Bool := true
  projectedTheoriesRevisable : Bool := true
  opinionsChangedManyTimes : Bool := true
  newMaterialWouldChangeViewsAgain : Bool := true
  incorrectConclusionsMayAssistInquiry : Bool := true
  moreAccurateKnowledgeProduced : Bool := true
deriving DecidableEq, Repr

def fragmentCorrectionDiscipline : FragmentCorrectionDiscipline := {}

def revisableFragmentMethod (f : FragmentCorrectionDiscipline) : Prop :=
  f.brokenFragmentsDifficult = true ∧
  f.projectedTheoriesRevisable = true ∧
  f.opinionsChangedManyTimes = true ∧
  f.newMaterialWouldChangeViewsAgain = true ∧
  f.incorrectConclusionsMayAssistInquiry = true ∧
  f.moreAccurateKnowledgeProduced = true

structure ErrorToTruthLadder where
  errorNamedAsPossibleStep : Bool := true
  truthNamedAsTarget : Bool := true
  cuneiformMattersRequireIteration : Bool := true
  failedTheoryCanExposeConstraint : Bool := true
  correctionKeepsInquiryAlive : Bool := true
deriving DecidableEq, Repr

def errorToTruthLadder : ErrorToTruthLadder := {}

def advancesThroughErrorToTruth (e : ErrorToTruthLadder) : Prop :=
  e.errorNamedAsPossibleStep = true ∧
  e.truthNamedAsTarget = true ∧
  e.cuneiformMattersRequireIteration = true ∧
  e.failedTheoryCanExposeConstraint = true ∧
  e.correctionKeepsInquiryAlive = true

structure EarlyHistoryValueClassifier where
  marvelsDoNotAutomaticallyVoidEvents : Bool := true
  generalRepudiationOfEarlyHistoryRejected : Bool := true
  naturalPhenomenaReductionHeldUnderReserve : Bool := true
  genuineTraditionsRecognized : Bool := true
  phenomenaExplanationsRecognized : Bool := true
  pureRomancesRecognized : Bool := true
deriving DecidableEq, Repr

def earlyHistoryValueClassifier : EarlyHistoryValueClassifier := {}

def mixedValueMythicArchive (m : EarlyHistoryValueClassifier) : Prop :=
  m.marvelsDoNotAutomaticallyVoidEvents = true ∧
  m.generalRepudiationOfEarlyHistoryRejected = true ∧
  m.naturalPhenomenaReductionHeldUnderReserve = true ∧
  m.genuineTraditionsRecognized = true ∧
  m.phenomenaExplanationsRecognized = true ∧
  m.pureRomancesRecognized = true

theorem error_to_truth_bounded_hazardous_theory :
    boundedHazardousTheory hazardousTheoryReserve := by
  unfold boundedHazardousTheory hazardousTheoryReserve
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem error_to_truth_revisable_fragment_method :
    revisableFragmentMethod fragmentCorrectionDiscipline := by
  unfold revisableFragmentMethod fragmentCorrectionDiscipline
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem error_to_truth_advances_through_error_to_truth :
    advancesThroughErrorToTruth errorToTruthLadder := by
  unfold advancesThroughErrorToTruth errorToTruthLadder
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem error_to_truth_mixed_value_mythic_archive :
    mixedValueMythicArchive earlyHistoryValueClassifier := by
  unfold mixedValueMythicArchive earlyHistoryValueClassifier
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem error_to_truth_inherits_fragment_recovery :
    ChaldeanGenesisFragmentRecoveryWitness.visibleProvisionalMethod
      ChaldeanGenesisFragmentRecoveryWitness.provisionalTranslationDiscipline ∧
    ChaldeanGenesisFragmentRecoveryWitness.materialArchiveHole
      ChaldeanGenesisFragmentRecoveryWitness.tabletArchiveDamage ∧
    revisableFragmentMethod fragmentCorrectionDiscipline := by
  exact ⟨ChaldeanGenesisFragmentRecoveryWitness.chaldean_visible_provisional_method,
    ChaldeanGenesisFragmentRecoveryWitness.chaldean_material_archive_hole,
    error_to_truth_revisable_fragment_method⟩

theorem error_to_truth_inherits_comparative_reserve :
    ComparativeFloodMethodReserveWitness.comparisonHeldUnderReserve
      ComparativeFloodMethodReserveWitness.comparativeReserve ∧
    ComparativeFloodMethodReserveWitness.sharedTopologyWithoutCopyClaim
      ComparativeFloodMethodReserveWitness.correspondenceWithoutDirectCopy ∧
    boundedHazardousTheory hazardousTheoryReserve := by
  exact ⟨ComparativeFloodMethodReserveWitness.comparative_comparison_held_under_reserve,
    ComparativeFloodMethodReserveWitness.comparative_shared_topology_without_copy_claim,
    error_to_truth_bounded_hazardous_theory⟩

theorem error_to_truth_preserves_chaos_source_under_classifier :
    MummuTiamatuPleromaMattressWitness.hiddenSubstrateWitness
      MummuTiamatuPleromaMattressWitness.mummuTiamatuHiddenSubstrate ∧
    mixedValueMythicArchive earlyHistoryValueClassifier := by
  exact ⟨MummuTiamatuPleromaMattressWitness.mummu_tiamatu_hidden_substrate,
    error_to_truth_mixed_value_mythic_archive⟩

theorem error_to_truth_fragment_method_witness :
    boundedHazardousTheory hazardousTheoryReserve ∧
    revisableFragmentMethod fragmentCorrectionDiscipline ∧
    advancesThroughErrorToTruth errorToTruthLadder ∧
    mixedValueMythicArchive earlyHistoryValueClassifier := by
  exact ⟨error_to_truth_bounded_hazardous_theory,
    error_to_truth_revisable_fragment_method,
    error_to_truth_advances_through_error_to_truth,
    error_to_truth_mixed_value_mythic_archive⟩

end ErrorToTruthFragmentMethodWitness
end Gnosis.Witnesses.Chaldean
