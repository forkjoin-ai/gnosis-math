import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAzZumarSuraQualityWitness

/-!
# Quran 39, Al-Zumar / The Throngs -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:12010-12170`.

This complete sura witness covers Quran 39:1-75.

Al-Zumar is the pure-devotion-and-thronged-return witness. Scripture sent down
with Truth, total devotion, false protectors claiming nearness, no divine
offspring, purposeful creation, night and day wrapped over each other, womb
formation, gratitude, night worship, the wide earth, shunning false gods, the
best consistent discourse softening skins and hearts, one master against many
partners, God as sufficient, free choice under guidance, sleep and death souls,
intercession held by God, mercy against despair, repentance before closure, the
Trumpet, earth shining by its Lord, records, prophets, witnesses, and throngs to
Hell and Garden all witness return as sorted disclosure.

No `sorry`, no new `axiom`.
-/

inductive ZumarQualityCluster
  | truthScripturePureDevotionAndFalseNearness
  | purposefulCreationWrappedTimeWombsAndGratitude
  | nightWorshipWideEarthConsistentDiscourseAndGuidance
  | sleepDeathIntercessionMercyAndRepentanceBoundary
  | trumpetRecordsWitnessesAndThrongs
deriving DecidableEq, Repr

def zumarQualityClusters : List ZumarQualityCluster :=
  [ ZumarQualityCluster.truthScripturePureDevotionAndFalseNearness
  , ZumarQualityCluster.purposefulCreationWrappedTimeWombsAndGratitude
  , ZumarQualityCluster.nightWorshipWideEarthConsistentDiscourseAndGuidance
  , ZumarQualityCluster.sleepDeathIntercessionMercyAndRepentanceBoundary
  , ZumarQualityCluster.trumpetRecordsWitnessesAndThrongs
  ]

structure ZumarInvariantLedger where
  devotionBelongsPurelyToGod : Bool := true
  creationAndTimeAreOrderedInTruth : Bool := true
  bestDiscourseSoftensTowardGuidance : Bool := true
  soulsInSleepAndDeathRemainHeldByGod : Bool := true
  mercyInvitesRepentanceBeforeClosure : Bool := true
  finalRecordsSortThrongsWithWitnesses : Bool := true
deriving DecidableEq, Repr

def zumarInvariantLedger : ZumarInvariantLedger := {}

def zumarSat (l : ZumarInvariantLedger) : Prop :=
  l.devotionBelongsPurelyToGod = true ∧
  l.creationAndTimeAreOrderedInTruth = true ∧
  l.bestDiscourseSoftensTowardGuidance = true ∧
  l.soulsInSleepAndDeathRemainHeldByGod = true ∧
  l.mercyInvitesRepentanceBeforeClosure = true ∧
  l.finalRecordsSortThrongsWithWitnesses = true

structure ZumarGapLedger where
  protectorsClaimFalseNearness : Bool := true
  partnersSplitOneServantIntoManyMasters : Bool := true
  GodIsNotDeemedSufficient : Bool := true
  despairMisreadsMercy : Bool := true
  lateRegretCannotBuyReturn : Bool := true
  arrogantRejectersArriveInThrongs : Bool := true
deriving DecidableEq, Repr

def zumarGapLedger : ZumarGapLedger := {}

def zumarGapsExposeBoundary (g : ZumarGapLedger) : Prop :=
  g.protectorsClaimFalseNearness = true ∧
  g.partnersSplitOneServantIntoManyMasters = true ∧
  g.GodIsNotDeemedSufficient = true ∧
  g.despairMisreadsMercy = true ∧
  g.lateRegretCannotBuyReturn = true ∧
  g.arrogantRejectersArriveInThrongs = true

def zumarSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 39 / Al-Zumar witnesses pure devotion, mercy-before-closure, and sorted return"
    positiveSamples := [1, 2, 3, 4, 5, 6]
    negativeSamples := [7, 8, 9, 10, 11, 12] }

inductive ZumarRegister | scripture | devotion | time | discourse | souls | mercy | throngs
deriving DecidableEq, Repr, Nonempty

inductive ZumarInvariant | pureDevotionSortedReturn
deriving DecidableEq, Repr

def zumarRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : ZumarRegister => ZumarInvariant.pureDevotionSortedReturn)
      ZumarInvariant.pureDevotionSortedReturn :=
  TruthOneManyNamesWitness.constant_names_agree ZumarInvariant.pureDevotionSortedReturn

theorem zumar_quality_clusters_shape :
    zumarQualityClusters.length = 5
    ∧ zumarQualityClusters.head? =
      some ZumarQualityCluster.truthScripturePureDevotionAndFalseNearness
    ∧ zumarQualityClusters.getLast? =
      some ZumarQualityCluster.trumpetRecordsWitnessesAndThrongs := by
  exact ⟨rfl, rfl, rfl⟩

theorem zumar_sat_witness : zumarSat zumarInvariantLedger := by
  unfold zumarSat zumarInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem zumar_gap_witness : zumarGapsExposeBoundary zumarGapLedger := by
  unfold zumarGapsExposeBoundary zumarGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem zumar_access_archaeological :
    zumarSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_az_zumar_sura_quality_witness :
    zumarQualityClusters.length = 5 ∧
    zumarSat zumarInvariantLedger ∧
    zumarGapsExposeBoundary zumarGapLedger ∧
    zumarSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : ZumarRegister => ZumarInvariant.pureDevotionSortedReturn)
      ZumarInvariant.pureDevotionSortedReturn := by
  exact ⟨zumar_quality_clusters_shape.left, zumar_sat_witness, zumar_gap_witness,
    zumar_access_archaeological, zumarRegistersAgree⟩

end QuranAzZumarSuraQualityWitness
end Gnosis.Witnesses.Islam
