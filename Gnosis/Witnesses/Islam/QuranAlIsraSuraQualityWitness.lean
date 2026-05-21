import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlIsraSuraQualityWitness

/-!
# Quran 17, Al-Isra / The Night Journey -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:7596-7887`.

This complete sura witness covers Quran 17:1-111.

Al-Isra is the record-and-guidance witness. Night journey, Israel's corruption
cycles, the straightest Quran, personal record, commandments, universal praise,
Iblis's delusive promise, sea-distress ingratitude, dawn recitation, healing
Quran, challenge to mankind and jinn, human-messenger boundary, Moses' signs,
and the best Names converge on accountable guidance. The counterproof is haste,
wealth-corrupted towns, child killing, blind following, arrogant strutting,
daughter claims, resurrection mockery, miracle shopping, and temptation to
invent revelation.

No `sorry`, no new `axiom`.
-/

inductive AlIsraQualityCluster
  | nightJourneyIsraelGuideAndCorruptionCycles
  | straightestQuranRecordAndStriving
  | commandmentsParentsGivingLifeAndMeasure
  | universalPraiseBarrierAndResurrectionMockery
  | bestSpeechIblisPromiseAndSeaIngratitude
  | rightHandRecordTemptationAndWitnessedPrayer
  | truthHealingSpiritAndQuranChallenge
  | miracleDemandsHumanMessengerAndMosesSigns
  | truthDescentEarlierKnowledgeAndBestNames
deriving DecidableEq, Repr

def alIsraQualityClusters : List AlIsraQualityCluster :=
  [ AlIsraQualityCluster.nightJourneyIsraelGuideAndCorruptionCycles
  , AlIsraQualityCluster.straightestQuranRecordAndStriving
  , AlIsraQualityCluster.commandmentsParentsGivingLifeAndMeasure
  , AlIsraQualityCluster.universalPraiseBarrierAndResurrectionMockery
  , AlIsraQualityCluster.bestSpeechIblisPromiseAndSeaIngratitude
  , AlIsraQualityCluster.rightHandRecordTemptationAndWitnessedPrayer
  , AlIsraQualityCluster.truthHealingSpiritAndQuranChallenge
  , AlIsraQualityCluster.miracleDemandsHumanMessengerAndMosesSigns
  , AlIsraQualityCluster.truthDescentEarlierKnowledgeAndBestNames
  ]

structure AlIsraInvariantLedger where
  quranShowsStraightestWay : Bool := true
  eachSoulReadsItsOwnRecord : Bool := true
  commandmentsProtectHumanDignity : Bool := true
  allThingsPraiseBeyondHumanHearing : Bool := true
  satanicPromiseHasNoAuthorityOverServants : Bool := true
  truthComesAndFalsehoodPasses : Bool := true
  quranIsHealingForBelievers : Bool := true
  humanMessengerLimitIsExplicit : Bool := true
  bestNamesCloseWithoutChildOrPartner : Bool := true
deriving DecidableEq, Repr

def alIsraInvariantLedger : AlIsraInvariantLedger := {}

def alIsraSat (l : AlIsraInvariantLedger) : Prop :=
  l.quranShowsStraightestWay = true ∧
  l.eachSoulReadsItsOwnRecord = true ∧
  l.commandmentsProtectHumanDignity = true ∧
  l.allThingsPraiseBeyondHumanHearing = true ∧
  l.satanicPromiseHasNoAuthorityOverServants = true ∧
  l.truthComesAndFalsehoodPasses = true ∧
  l.quranIsHealingForBelievers = true ∧
  l.humanMessengerLimitIsExplicit = true ∧
  l.bestNamesCloseWithoutChildOrPartner = true

structure AlIsraGapLedger where
  peoplePrayForHarmInHaste : Bool := true
  wealthyTownCorruptionPersists : Bool := true
  childKillingForPovertyFear : Bool := true
  blindFollowingWithoutKnowledge : Bool := true
  arrogantStrutting : Bool := true
  daughterClaimForAngels : Bool := true
  resurrectionBonesDustMockery : Bool := true
  seaRescueFollowedByIngratitude : Bool := true
  inventedRevelationTemptation : Bool := true
  miracleShoppingAgainstHumanMessenger : Bool := true
deriving DecidableEq, Repr

def alIsraGapLedger : AlIsraGapLedger := {}

def alIsraGapsExposeBoundary (g : AlIsraGapLedger) : Prop :=
  g.peoplePrayForHarmInHaste = true ∧
  g.wealthyTownCorruptionPersists = true ∧
  g.childKillingForPovertyFear = true ∧
  g.blindFollowingWithoutKnowledge = true ∧
  g.arrogantStrutting = true ∧
  g.daughterClaimForAngels = true ∧
  g.resurrectionBonesDustMockery = true ∧
  g.seaRescueFollowedByIngratitude = true ∧
  g.inventedRevelationTemptation = true ∧
  g.miracleShoppingAgainstHumanMessenger = true

def alIsraSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 17 / Al-Isra witnesses accountable guidance through record, command, and truth-descent"
    positiveSamples := [1, 2, 3, 4, 5, 6, 7]
    negativeSamples := [8, 9, 10, 11, 12, 13] }

inductive AlIsraRegister | journey | record | command | praise | iblis | prayer | healing | names
deriving DecidableEq, Repr, Nonempty

inductive AlIsraInvariant | accountableStraightGuidance
deriving DecidableEq, Repr

def alIsraRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AlIsraRegister => AlIsraInvariant.accountableStraightGuidance)
      AlIsraInvariant.accountableStraightGuidance :=
  TruthOneManyNamesWitness.constant_names_agree AlIsraInvariant.accountableStraightGuidance

theorem al_isra_quality_clusters_shape :
    alIsraQualityClusters.length = 9
    ∧ alIsraQualityClusters.head? =
      some AlIsraQualityCluster.nightJourneyIsraelGuideAndCorruptionCycles
    ∧ alIsraQualityClusters.getLast? =
      some AlIsraQualityCluster.truthDescentEarlierKnowledgeAndBestNames := by
  exact ⟨rfl, rfl, rfl⟩

theorem al_isra_sat_witness : alIsraSat alIsraInvariantLedger := by
  unfold alIsraSat alIsraInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem al_isra_gap_witness : alIsraGapsExposeBoundary alIsraGapLedger := by
  unfold alIsraGapsExposeBoundary alIsraGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem al_isra_access_archaeological :
    alIsraSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_al_isra_sura_quality_witness :
    alIsraQualityClusters.length = 9 ∧
    alIsraSat alIsraInvariantLedger ∧
    alIsraGapsExposeBoundary alIsraGapLedger ∧
    alIsraSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AlIsraRegister => AlIsraInvariant.accountableStraightGuidance)
      AlIsraInvariant.accountableStraightGuidance := by
  exact ⟨al_isra_quality_clusters_shape.left, al_isra_sat_witness, al_isra_gap_witness,
    al_isra_access_archaeological, alIsraRegistersAgree⟩

end QuranAlIsraSuraQualityWitness
end Gnosis.Witnesses.Islam
