import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranYasinSuraQualityWitness

/-!
# Quran 36, Ya Sin -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:11489-11616`.

This complete sura witness covers Quran 36:1-83.

Ya Sin is the recorded-trace-and-revival witness. The wise Quran, the straight
path, collars and barriers, warning those who follow the reminder, the record of
what agents send ahead and leave behind, the town messengers and running believer,
dead earth revived into grain, paired creation, night, sun, moon, Ark and ships,
refused charity, the single blast, Paradise peace, guilty separation, sealed
mouths with hands and feet testifying, Quran as warning rather than poetry,
livestock signs, open dispute from a drop, green-tree fire, and the command
"Be" converge on resurrection as trace recovery.

No `sorry`, no new `axiom`.
-/

inductive YasinQualityCluster
  | wiseQuranStraightPathAndBarrieredDenial
  | recordedTracesTownMessengersAndRunningBeliever
  | revivedEarthPairsNightSunMoonAndShips
  | blastParadisePeaceSealedMouthsAndLimbWitness
  | warningLivestockDropDisputeGreenFireAndBe
deriving DecidableEq, Repr

def yasinQualityClusters : List YasinQualityCluster :=
  [ YasinQualityCluster.wiseQuranStraightPathAndBarrieredDenial
  , YasinQualityCluster.recordedTracesTownMessengersAndRunningBeliever
  , YasinQualityCluster.revivedEarthPairsNightSunMoonAndShips
  , YasinQualityCluster.blastParadisePeaceSealedMouthsAndLimbWitness
  , YasinQualityCluster.warningLivestockDropDisputeGreenFireAndBe
  ]

structure YasinInvariantLedger where
  sentAheadAndLeftBehindAreRecorded : Bool := true
  reminderWarnsThoseWhoFearTheUnseen : Bool := true
  deadEarthRevivalImagesReturn : Bool := true
  cosmicCoursesRunByMeasure : Bool := true
  limbsCanWitnessWhenMouthsAreSealed : Bool := true
  creativeCommandCompletesReturn : Bool := true
deriving DecidableEq, Repr

def yasinInvariantLedger : YasinInvariantLedger := {}

def yasinSat (l : YasinInvariantLedger) : Prop :=
  l.sentAheadAndLeftBehindAreRecorded = true ∧
  l.reminderWarnsThoseWhoFearTheUnseen = true ∧
  l.deadEarthRevivalImagesReturn = true ∧
  l.cosmicCoursesRunByMeasure = true ∧
  l.limbsCanWitnessWhenMouthsAreSealed = true ∧
  l.creativeCommandCompletesReturn = true

structure YasinGapLedger where
  barriersBlockRejectedWarning : Bool := true
  townDeniesHumanMessengers : Bool := true
  charityRefusalMocksProvision : Bool := true
  resurrectionIsReducedToRottenBones : Bool := true
  poetryMisreadsWarning : Bool := true
  creatureFromDropBecomesOpenDisputer : Bool := true
deriving DecidableEq, Repr

def yasinGapLedger : YasinGapLedger := {}

def yasinGapsExposeBoundary (g : YasinGapLedger) : Prop :=
  g.barriersBlockRejectedWarning = true ∧
  g.townDeniesHumanMessengers = true ∧
  g.charityRefusalMocksProvision = true ∧
  g.resurrectionIsReducedToRottenBones = true ∧
  g.poetryMisreadsWarning = true ∧
  g.creatureFromDropBecomesOpenDisputer = true

def yasinSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 36 / Ya Sin witnesses trace recording, earth revival, limb testimony, and return"
    positiveSamples := [1, 2, 3, 4, 5, 6]
    negativeSamples := [7, 8, 9, 10, 11, 12] }

inductive YasinRegister | quran | trace | town | earth | cosmos | limbs | command
deriving DecidableEq, Repr, Nonempty

inductive YasinInvariant | recordedTraceRevivalReturn
deriving DecidableEq, Repr

def yasinRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : YasinRegister => YasinInvariant.recordedTraceRevivalReturn)
      YasinInvariant.recordedTraceRevivalReturn :=
  TruthOneManyNamesWitness.constant_names_agree YasinInvariant.recordedTraceRevivalReturn

theorem yasin_quality_clusters_shape :
    yasinQualityClusters.length = 5
    ∧ yasinQualityClusters.head? =
      some YasinQualityCluster.wiseQuranStraightPathAndBarrieredDenial
    ∧ yasinQualityClusters.getLast? =
      some YasinQualityCluster.warningLivestockDropDisputeGreenFireAndBe := by
  exact ⟨rfl, rfl, rfl⟩

theorem yasin_sat_witness : yasinSat yasinInvariantLedger := by
  unfold yasinSat yasinInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem yasin_gap_witness : yasinGapsExposeBoundary yasinGapLedger := by
  unfold yasinGapsExposeBoundary yasinGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem yasin_access_archaeological :
    yasinSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_yasin_sura_quality_witness :
    yasinQualityClusters.length = 5 ∧
    yasinSat yasinInvariantLedger ∧
    yasinGapsExposeBoundary yasinGapLedger ∧
    yasinSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : YasinRegister => YasinInvariant.recordedTraceRevivalReturn)
      YasinInvariant.recordedTraceRevivalReturn := by
  exact ⟨yasin_quality_clusters_shape.left, yasin_sat_witness, yasin_gap_witness,
    yasin_access_archaeological, yasinRegistersAgree⟩

end QuranYasinSuraQualityWitness
end Gnosis.Witnesses.Islam
