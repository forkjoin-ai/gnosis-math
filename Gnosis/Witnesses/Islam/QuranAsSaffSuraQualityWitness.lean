import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAsSaffSuraQualityWitness

/-!
# Quran 61, As-Saff / Solid Lines -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:14525-14561`.

This complete sura witness covers Quran 61:1-14.

As-Saff is the speech-action-and-formation witness: all creation glorifies God,
believers are challenged not to say what they do not do, God loves those who
fight in solid lines, Moses' people swerve after knowledge, Jesus announces a
messenger after him, falsehood tries to extinguish God's light, and the disciples
model helper allegiance.

No `sorry`, no new `axiom`.
-/

inductive SaffQualityCluster
  | glorificationAndSpeechActionIntegrity
  | solidLineFormationAndBelovedOrder
  | mosesSwerveAndHeartDeviation
  | jesusAnnouncementAndLightUnextinguished
  | tradeForgivenessAndHelperAllegiance
deriving DecidableEq, Repr

def saffQualityClusters : List SaffQualityCluster :=
  [ .glorificationAndSpeechActionIntegrity, .solidLineFormationAndBelovedOrder,
    .mosesSwerveAndHeartDeviation, .jesusAnnouncementAndLightUnextinguished,
    .tradeForgivenessAndHelperAllegiance ]

structure SaffInvariantLedger where
  speechMustMatchAction : Bool := true
  orderedFormationCanServeTruth : Bool := true
  divineLightCannotBeExtinguished : Bool := true
  faithfulTradeYieldsForgiveness : Bool := true
  helpersStandWithRevelation : Bool := true
deriving DecidableEq, Repr

def saffInvariantLedger : SaffInvariantLedger := {}

def saffSat (l : SaffInvariantLedger) : Prop :=
  l.speechMustMatchAction = true ∧ l.orderedFormationCanServeTruth = true ∧
  l.divineLightCannotBeExtinguished = true ∧ l.faithfulTradeYieldsForgiveness = true ∧
  l.helpersStandWithRevelation = true

structure SaffGapLedger where
  sayingWithoutDoingIsHated : Bool := true
  knownMessengerCanStillBeHarmed : Bool := true
  heartsDeviateAfterChosenDeviation : Bool := true
  sorceryChargeMisreadsClearProof : Bool := true
  mouthsTryToExtinguishLight : Bool := true
deriving DecidableEq, Repr

def saffGapLedger : SaffGapLedger := {}

def saffGapsExposeBoundary (g : SaffGapLedger) : Prop :=
  g.sayingWithoutDoingIsHated = true ∧ g.knownMessengerCanStillBeHarmed = true ∧
  g.heartsDeviateAfterChosenDeviation = true ∧ g.sorceryChargeMisreadsClearProof = true ∧
  g.mouthsTryToExtinguishLight = true

def saffSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 61 / As-Saff witnesses speech-action integrity, solid formation, and helper allegiance"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive SaffRegister | speech | line | moses | jesus | light | helpers
deriving DecidableEq, Repr, Nonempty

inductive SaffInvariant | speechActionFormation
deriving DecidableEq, Repr

def saffRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : SaffRegister => SaffInvariant.speechActionFormation)
      SaffInvariant.speechActionFormation :=
  TruthOneManyNamesWitness.constant_names_agree SaffInvariant.speechActionFormation

theorem saff_quality_clusters_shape :
    saffQualityClusters.length = 5 ∧
    saffQualityClusters.head? = some .glorificationAndSpeechActionIntegrity ∧
    saffQualityClusters.getLast? = some .tradeForgivenessAndHelperAllegiance := by
  exact ⟨rfl, rfl, rfl⟩

theorem saff_sat_witness : saffSat saffInvariantLedger := by
  unfold saffSat saffInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem saff_gap_witness : saffGapsExposeBoundary saffGapLedger := by
  unfold saffGapsExposeBoundary saffGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem saff_access_archaeological :
    saffSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_as_saff_sura_quality_witness :
    saffQualityClusters.length = 5 ∧ saffSat saffInvariantLedger ∧
    saffGapsExposeBoundary saffGapLedger ∧
    saffSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : SaffRegister => SaffInvariant.speechActionFormation)
      SaffInvariant.speechActionFormation := by
  exact ⟨saff_quality_clusters_shape.left, saff_sat_witness, saff_gap_witness,
    saff_access_archaeological, saffRegistersAgree⟩

end QuranAsSaffSuraQualityWitness
end Gnosis.Witnesses.Islam
