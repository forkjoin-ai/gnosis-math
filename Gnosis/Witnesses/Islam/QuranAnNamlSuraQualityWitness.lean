import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAnNamlSuraQualityWitness

/-!
# Quran 27, An-Naml / The Ants -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:9956-10167`.

This complete sura witness covers Quran 27:1-93.

An-Naml is the knowledge-and-signs witness. Clear Quran, Moses' fire, David and
Solomon's knowledge, the ant's warning, the hoopoe's intelligence, Sheba's
submission, Salih's plotted night attack, Lot's rescue, the repeated "Is it
another god beside God?" proof chain, hidden knowledge, final gathering, and
the command to recite all converge on grateful knowledge under one Lord.

No `sorry`, no new `axiom`.
-/

inductive AnNamlQualityCluster
  | clearQuranMosesFireAndNineSigns
  | davidSolomonKnowledgeAntAndGratitude
  | hoopoeShebaThroneAndGlassSubmission
  | salihPlotLotRescueAndDestroyedHomes
  | godPowerQuestionsUnseenRecordAndFinalRecitation
deriving DecidableEq, Repr

def anNamlQualityClusters : List AnNamlQualityCluster :=
  [ AnNamlQualityCluster.clearQuranMosesFireAndNineSigns
  , AnNamlQualityCluster.davidSolomonKnowledgeAntAndGratitude
  , AnNamlQualityCluster.hoopoeShebaThroneAndGlassSubmission
  , AnNamlQualityCluster.salihPlotLotRescueAndDestroyedHomes
  , AnNamlQualityCluster.godPowerQuestionsUnseenRecordAndFinalRecitation
  ]

structure AnNamlInvariantLedger where
  quranGuidesAndWarns : Bool := true
  knowledgeRequiresGratitude : Bool := true
  hiddenThingsBelongToGod : Bool := true
  powerIsTestedBySubmission : Bool := true
  godAloneAnswersDistressAndCreates : Bool := true
  finalRecitationLeavesChoiceAccountable : Bool := true
deriving DecidableEq, Repr

def anNamlInvariantLedger : AnNamlInvariantLedger := {}

def anNamlSat (l : AnNamlInvariantLedger) : Prop :=
  l.quranGuidesAndWarns = true ∧
  l.knowledgeRequiresGratitude = true ∧
  l.hiddenThingsBelongToGod = true ∧
  l.powerIsTestedBySubmission = true ∧
  l.godAloneAnswersDistressAndCreates = true ∧
  l.finalRecitationLeavesChoiceAccountable = true

structure AnNamlGapLedger where
  deedsMadeAlluringWithoutHereafter : Bool := true
  signsDeniedDespiteSoulAcknowledgment : Bool := true
  sunWorshipBlocksRightPath : Bool := true
  rushingBadBeforeGood : Bool := true
  nightAttackPlot : Bool := true
  resurrectionAncientFables : Bool := true
  deadDeafBlindCannotBeForced : Bool := true
  denialWithoutComprehension : Bool := true
deriving DecidableEq, Repr

def anNamlGapLedger : AnNamlGapLedger := {}

def anNamlGapsExposeBoundary (g : AnNamlGapLedger) : Prop :=
  g.deedsMadeAlluringWithoutHereafter = true ∧
  g.signsDeniedDespiteSoulAcknowledgment = true ∧
  g.sunWorshipBlocksRightPath = true ∧
  g.rushingBadBeforeGood = true ∧
  g.nightAttackPlot = true ∧
  g.resurrectionAncientFables = true ∧
  g.deadDeafBlindCannotBeForced = true ∧
  g.denialWithoutComprehension = true

def anNamlSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 27 / An-Naml witnesses grateful knowledge, creature warning, and one-God proof"
    positiveSamples := [1, 2, 3, 4, 5, 6]
    negativeSamples := [7, 8, 9, 10, 11, 12] }

inductive AnNamlRegister | quran | moses | ant | hoopoe | sheba | plots | questions | recitation
deriving DecidableEq, Repr, Nonempty

inductive AnNamlInvariant | gratefulKnowledgeSigns
deriving DecidableEq, Repr

def anNamlRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AnNamlRegister => AnNamlInvariant.gratefulKnowledgeSigns)
      AnNamlInvariant.gratefulKnowledgeSigns :=
  TruthOneManyNamesWitness.constant_names_agree AnNamlInvariant.gratefulKnowledgeSigns

theorem an_naml_quality_clusters_shape :
    anNamlQualityClusters.length = 5
    ∧ anNamlQualityClusters.head? = some AnNamlQualityCluster.clearQuranMosesFireAndNineSigns
    ∧ anNamlQualityClusters.getLast? =
      some AnNamlQualityCluster.godPowerQuestionsUnseenRecordAndFinalRecitation := by
  exact ⟨rfl, rfl, rfl⟩

theorem an_naml_sat_witness : anNamlSat anNamlInvariantLedger := by
  unfold anNamlSat anNamlInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem an_naml_gap_witness : anNamlGapsExposeBoundary anNamlGapLedger := by
  unfold anNamlGapsExposeBoundary anNamlGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem an_naml_access_archaeological :
    anNamlSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_an_naml_sura_quality_witness :
    anNamlQualityClusters.length = 5 ∧
    anNamlSat anNamlInvariantLedger ∧
    anNamlGapsExposeBoundary anNamlGapLedger ∧
    anNamlSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AnNamlRegister => AnNamlInvariant.gratefulKnowledgeSigns)
      AnNamlInvariant.gratefulKnowledgeSigns := by
  exact ⟨an_naml_quality_clusters_shape.left, an_naml_sat_witness, an_naml_gap_witness,
    an_naml_access_archaeological, anNamlRegistersAgree⟩

end QuranAnNamlSuraQualityWitness
end Gnosis.Witnesses.Islam
