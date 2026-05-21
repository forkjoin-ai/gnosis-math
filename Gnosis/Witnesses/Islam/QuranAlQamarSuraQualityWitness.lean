import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlQamarSuraQualityWitness

/-!
# Quran 54, Al-Qamar / The Moon -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:13849-13926`.

This complete sura witness covers Quran 54:1-55.

Al-Qamar is the repeated-warning-and-easy-reminder witness. The Hour draws near
and the moon splits; signs are dismissed as lasting sorcery; Noah, Ad, Thamud,
Lot, and Pharaoh recur as warnings; the refrain that the Quran is made easy for
remembrance tests whether anyone will be mindful; everything is measured and
recorded; and the mindful end in a seat of truth.

No `sorry`, no new `axiom`.
-/

inductive QamarQualityCluster
  | nearHourSplitMoonAndDismissedSigns
  | noahArkAndRememberedWarning
  | adThamudAndSingleCryMeasure
  | lotPharaohAndMorningJudgment
  | easyReminderRecordMeasureAndTruthSeat
deriving DecidableEq, Repr

def qamarQualityClusters : List QamarQualityCluster :=
  [ .nearHourSplitMoonAndDismissedSigns
  , .noahArkAndRememberedWarning
  , .adThamudAndSingleCryMeasure
  , .lotPharaohAndMorningJudgment
  , .easyReminderRecordMeasureAndTruthSeat
  ]

structure QamarInvariantLedger where
  signsWarnBeforeTheHour : Bool := true
  quranIsMadeEasyForRemembrance : Bool := true
  repeatedTownCyclesExposeOnePattern : Bool := true
  everythingIsCreatedByMeasure : Bool := true
  deedsAreRecordedBeforeTruthSeat : Bool := true
deriving DecidableEq, Repr

def qamarInvariantLedger : QamarInvariantLedger := {}

def qamarSat (l : QamarInvariantLedger) : Prop :=
  l.signsWarnBeforeTheHour = true ∧
  l.quranIsMadeEasyForRemembrance = true ∧
  l.repeatedTownCyclesExposeOnePattern = true ∧
  l.everythingIsCreatedByMeasure = true ∧
  l.deedsAreRecordedBeforeTruthSeat = true

structure QamarGapLedger where
  splitMoonIsDismissedAsSorcery : Bool := true
  warningsAreCalledHumanLies : Bool := true
  measuredMiracleIsMetByDefiance : Bool := true
  seizedNationsDoNotInterruptDenialPattern : Bool := true
  criminalsEnterFireAfterRecordExposure : Bool := true
deriving DecidableEq, Repr

def qamarGapLedger : QamarGapLedger := {}

def qamarGapsExposeBoundary (g : QamarGapLedger) : Prop :=
  g.splitMoonIsDismissedAsSorcery = true ∧
  g.warningsAreCalledHumanLies = true ∧
  g.measuredMiracleIsMetByDefiance = true ∧
  g.seizedNationsDoNotInterruptDenialPattern = true ∧
  g.criminalsEnterFireAfterRecordExposure = true

def qamarSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 54 / Al-Qamar witnesses repeated warning, easy remembrance, and measured record"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive QamarRegister | moon | noah | ad | thamud | lot | record
deriving DecidableEq, Repr, Nonempty

inductive QamarInvariant | measuredRepeatedReminder
deriving DecidableEq, Repr

def qamarRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : QamarRegister => QamarInvariant.measuredRepeatedReminder)
      QamarInvariant.measuredRepeatedReminder :=
  TruthOneManyNamesWitness.constant_names_agree QamarInvariant.measuredRepeatedReminder

theorem qamar_quality_clusters_shape :
    qamarQualityClusters.length = 5 ∧
    qamarQualityClusters.head? = some .nearHourSplitMoonAndDismissedSigns ∧
    qamarQualityClusters.getLast? = some .easyReminderRecordMeasureAndTruthSeat := by
  exact ⟨rfl, rfl, rfl⟩

theorem qamar_sat_witness : qamarSat qamarInvariantLedger := by
  unfold qamarSat qamarInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem qamar_gap_witness : qamarGapsExposeBoundary qamarGapLedger := by
  unfold qamarGapsExposeBoundary qamarGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem qamar_access_archaeological :
    qamarSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_al_qamar_sura_quality_witness :
    qamarQualityClusters.length = 5 ∧
    qamarSat qamarInvariantLedger ∧
    qamarGapsExposeBoundary qamarGapLedger ∧
    qamarSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : QamarRegister => QamarInvariant.measuredRepeatedReminder)
      QamarInvariant.measuredRepeatedReminder := by
  exact ⟨qamar_quality_clusters_shape.left, qamar_sat_witness, qamar_gap_witness,
    qamar_access_archaeological, qamarRegistersAgree⟩

end QuranAlQamarSuraQualityWitness
end Gnosis.Witnesses.Islam
