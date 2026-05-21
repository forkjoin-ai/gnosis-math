import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlQalamSuraQualityWitness

/-!
# Quran 68, Al-Qalam / The Pen -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:14922-14990`.

This complete sura witness covers Quran 68:1-52.

Al-Qalam is the inscription-and-garden-test witness. The Pen and what is written
defend prophetic sanity, bad character is listed as a negative witness, the
garden owners swear to harvest without acknowledging dependency, their garden is
stripped, Jonah's swallowed distress models patient repair, and hostile stares
cannot turn the reminder into madness.

No `sorry`, no new `axiom`.
-/

inductive QalamQualityCluster
  | penOathAndPropheticCharacter
  | slanderousCharacterCounterLedger
  | gardenOwnersAndWithheldException
  | strippedGardenRecognitionAndRepentance
  | jonahPatienceHostileStaresAndReminder
deriving DecidableEq, Repr

def qalamQualityClusters : List QalamQualityCluster :=
  [ .penOathAndPropheticCharacter, .slanderousCharacterCounterLedger,
    .gardenOwnersAndWithheldException, .strippedGardenRecognitionAndRepentance,
    .jonahPatienceHostileStaresAndReminder ]

structure QalamInvariantLedger where
  inscriptionWitnessesPropheticSanity : Bool := true
  characterRevealsTruthAlignment : Bool := true
  provisionRequiresAcknowledgedDependency : Bool := true
  strippedGardenCanExposeRepair : Bool := true
  patienceProtectsMessengerUnderHostility : Bool := true
deriving DecidableEq, Repr

def qalamInvariantLedger : QalamInvariantLedger := {}

def qalamSat (l : QalamInvariantLedger) : Prop :=
  l.inscriptionWitnessesPropheticSanity = true ∧ l.characterRevealsTruthAlignment = true ∧
  l.provisionRequiresAcknowledgedDependency = true ∧ l.strippedGardenCanExposeRepair = true ∧
  l.patienceProtectsMessengerUnderHostility = true

structure QalamGapLedger where
  madnessChargeMasksReminder : Bool := true
  slanderOathHabitExposesCorruptCharacter : Bool := true
  harvestPlanExcludesPoorAndGodWilling : Bool := true
  punishmentCanArriveBeforeMorning : Bool := true
  hostileGazeTriesToDislodgeMessenger : Bool := true
deriving DecidableEq, Repr

def qalamGapLedger : QalamGapLedger := {}

def qalamGapsExposeBoundary (g : QalamGapLedger) : Prop :=
  g.madnessChargeMasksReminder = true ∧ g.slanderOathHabitExposesCorruptCharacter = true ∧
  g.harvestPlanExcludesPoorAndGodWilling = true ∧ g.punishmentCanArriveBeforeMorning = true ∧
  g.hostileGazeTriesToDislodgeMessenger = true

def qalamSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 68 / Al-Qalam witnesses inscription, character, garden dependency, and patient repair"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive QalamRegister | pen | character | garden | dependency | jonah | reminder
deriving DecidableEq, Repr, Nonempty

inductive QalamInvariant | inscribedCharacterDependency
deriving DecidableEq, Repr

def qalamRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : QalamRegister => QalamInvariant.inscribedCharacterDependency)
      QalamInvariant.inscribedCharacterDependency :=
  TruthOneManyNamesWitness.constant_names_agree QalamInvariant.inscribedCharacterDependency

theorem qalam_quality_clusters_shape :
    qalamQualityClusters.length = 5 ∧ qalamQualityClusters.head? = some .penOathAndPropheticCharacter ∧
    qalamQualityClusters.getLast? = some .jonahPatienceHostileStaresAndReminder := by
  exact ⟨rfl, rfl, rfl⟩

theorem qalam_sat_witness : qalamSat qalamInvariantLedger := by
  unfold qalamSat qalamInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem qalam_gap_witness : qalamGapsExposeBoundary qalamGapLedger := by
  unfold qalamGapsExposeBoundary qalamGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem qalam_access_archaeological :
    qalamSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_al_qalam_sura_quality_witness :
    qalamQualityClusters.length = 5 ∧ qalamSat qalamInvariantLedger ∧
    qalamGapsExposeBoundary qalamGapLedger ∧
    qalamSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : QalamRegister => QalamInvariant.inscribedCharacterDependency)
      QalamInvariant.inscribedCharacterDependency := by
  exact ⟨qalam_quality_clusters_shape.left, qalam_sat_witness, qalam_gap_witness,
    qalam_access_archaeological, qalamRegistersAgree⟩

end QuranAlQalamSuraQualityWitness
end Gnosis.Witnesses.Islam
