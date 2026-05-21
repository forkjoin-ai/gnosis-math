import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlInsanSuraQualityWitness

/-! # Quran 76, Al-Insan / Man -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:15379-15415`.
This witness covers Quran 76:1-31: human emergence from nothing notable, tested
hearing and sight, feeding for God's face, patient Garden reward, and revelation
as reminder against choosing only the passing life. No `sorry`, no new `axiom`. -/

inductive InsanQualityCluster
  | unmentionedHumanAndMixedDropTest | pathGratitudeOrIngratitude
  | feedingPoorOrphanCaptiveForGod | patientGardenRewardAndSilk
  | quranReminderPassingLifeAndMercyChoice
deriving DecidableEq, Repr

def insanQualityClusters : List InsanQualityCluster :=
  [ .unmentionedHumanAndMixedDropTest, .pathGratitudeOrIngratitude,
    .feedingPoorOrphanCaptiveForGod, .patientGardenRewardAndSilk,
    .quranReminderPassingLifeAndMercyChoice ]

structure InsanInvariantLedger where
  humanFacultiesAreTestedGifts : Bool := true
  pathIsShownBeforeChoice : Bool := true
  givingForGodsFaceNeedsNoReturn : Bool := true
  patienceReceivesGardenReward : Bool := true
  mercyAdmitsWhomGodWills : Bool := true
deriving DecidableEq, Repr
def insanInvariantLedger : InsanInvariantLedger := {}
def insanSat (l : InsanInvariantLedger) : Prop :=
  l.humanFacultiesAreTestedGifts = true ∧ l.pathIsShownBeforeChoice = true ∧
  l.givingForGodsFaceNeedsNoReturn = true ∧ l.patienceReceivesGardenReward = true ∧
  l.mercyAdmitsWhomGodWills = true

structure InsanGapLedger where
  ingratitudeChoosesChains : Bool := true
  passingLifeIsPreferred : Bool := true
  gratitudeCanBeReplacedBySelfCredit : Bool := true
  warningCanBeIgnoredDespiteReminder : Bool := true
  wrongdoingRemainsOutsideMercyChoice : Bool := true
deriving DecidableEq, Repr
def insanGapLedger : InsanGapLedger := {}
def insanGapsExposeBoundary (g : InsanGapLedger) : Prop :=
  g.ingratitudeChoosesChains = true ∧ g.passingLifeIsPreferred = true ∧
  g.gratitudeCanBeReplacedBySelfCredit = true ∧ g.warningCanBeIgnoredDespiteReminder = true ∧
  g.wrongdoingRemainsOutsideMercyChoice = true

def insanSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 76 / Al-Insan witnesses tested faculties, selfless feeding, and patient reward"
    positiveSamples := [1, 2, 3, 4, 5], negativeSamples := [6, 7, 8, 9, 10] }
inductive InsanRegister | origin | test | path | feeding | patience | mercy
deriving DecidableEq, Repr, Nonempty
inductive InsanInvariant | testedMercifulHumanPath deriving DecidableEq, Repr
def insanRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : InsanRegister => InsanInvariant.testedMercifulHumanPath)
      InsanInvariant.testedMercifulHumanPath :=
  TruthOneManyNamesWitness.constant_names_agree InsanInvariant.testedMercifulHumanPath

theorem insan_quality_clusters_shape :
    insanQualityClusters.length = 5 ∧ insanQualityClusters.head? = some .unmentionedHumanAndMixedDropTest ∧
    insanQualityClusters.getLast? = some .quranReminderPassingLifeAndMercyChoice := by exact ⟨rfl, rfl, rfl⟩
theorem insan_sat_witness : insanSat insanInvariantLedger := by
  unfold insanSat insanInvariantLedger; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem insan_gap_witness : insanGapsExposeBoundary insanGapLedger := by
  unfold insanGapsExposeBoundary insanGapLedger; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem insan_access_archaeological :
    insanSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by rfl
theorem quran_al_insan_sura_quality_witness :
    insanQualityClusters.length = 5 ∧ insanSat insanInvariantLedger ∧ insanGapsExposeBoundary insanGapLedger ∧
    insanSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : InsanRegister => InsanInvariant.testedMercifulHumanPath)
      InsanInvariant.testedMercifulHumanPath := by
  exact ⟨insan_quality_clusters_shape.left, insan_sat_witness, insan_gap_witness,
    insan_access_archaeological, insanRegistersAgree⟩

end QuranAlInsanSuraQualityWitness
end Gnosis.Witnesses.Islam
