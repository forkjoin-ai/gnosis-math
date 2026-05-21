import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlMaarijSuraQualityWitness

/-!
# Quran 70, Al-Ma'arij / The Ways of Ascent -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:15057-15092`.

This complete sura witness covers Quran 70:1-44.

Al-Ma'arij is the ascent-and-impatient-human witness. A demanded punishment
comes from the Lord of ascending ways; angels and Spirit ascend on the long Day;
kinship cannot ransom the guilty; humans are anxious and withholding except
prayer-keepers, alms-givers, truth-affirmers, chastity-guarders, trust-keepers,
and testimony-standers; and the deniers rush toward a promised Day.

No `sorry`, no new `axiom`.
-/

inductive MaarijQualityCluster
  | demandedPunishmentAndAscendingWays
  | longDayAndFailedKinshipRansom
  | anxiousWithholdingHumanCountertype
  | prayerAlmsTrustChastityAndTestimony
  | rushingDeniersAndPromisedDay
deriving DecidableEq, Repr

def maarijQualityClusters : List MaarijQualityCluster :=
  [ .demandedPunishmentAndAscendingWays, .longDayAndFailedKinshipRansom,
    .anxiousWithholdingHumanCountertype, .prayerAlmsTrustChastityAndTestimony,
    .rushingDeniersAndPromisedDay ]

structure MaarijInvariantLedger where
  ascentBelongsToGodsCommand : Bool := true
  kinshipCannotRansomTheGuilty : Bool := true
  disciplinedPracticeRepairsHumanAnxiety : Bool := true
  trustsAndTestimoniesMustBeMaintained : Bool := true
  promisedDayArrivesDespiteMockery : Bool := true
deriving DecidableEq, Repr

def maarijInvariantLedger : MaarijInvariantLedger := {}

def maarijSat (l : MaarijInvariantLedger) : Prop :=
  l.ascentBelongsToGodsCommand = true ∧ l.kinshipCannotRansomTheGuilty = true ∧
  l.disciplinedPracticeRepairsHumanAnxiety = true ∧ l.trustsAndTestimoniesMustBeMaintained = true ∧
  l.promisedDayArrivesDespiteMockery = true

structure MaarijGapLedger where
  punishmentDemandMocksItsOwnArrival : Bool := true
  familyRansomFantasyFails : Bool := true
  humanNaturePanicsAndWithholds : Bool := true
  deniersRushInGroupsWithoutUnderstanding : Bool := true
  promisedDayTurnsMockeryIntoHumiliation : Bool := true
deriving DecidableEq, Repr

def maarijGapLedger : MaarijGapLedger := {}

def maarijGapsExposeBoundary (g : MaarijGapLedger) : Prop :=
  g.punishmentDemandMocksItsOwnArrival = true ∧ g.familyRansomFantasyFails = true ∧
  g.humanNaturePanicsAndWithholds = true ∧ g.deniersRushInGroupsWithoutUnderstanding = true ∧
  g.promisedDayTurnsMockeryIntoHumiliation = true

def maarijSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 70 / Al-Ma'arij witnesses ascent, failed ransom, disciplined repair, and promised Day"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive MaarijRegister | ascent | day | kinship | prayer | trust | promise
deriving DecidableEq, Repr, Nonempty

inductive MaarijInvariant | ascentDisciplinedRepair
deriving DecidableEq, Repr

def maarijRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : MaarijRegister => MaarijInvariant.ascentDisciplinedRepair)
      MaarijInvariant.ascentDisciplinedRepair :=
  TruthOneManyNamesWitness.constant_names_agree MaarijInvariant.ascentDisciplinedRepair

theorem maarij_quality_clusters_shape :
    maarijQualityClusters.length = 5 ∧ maarijQualityClusters.head? = some .demandedPunishmentAndAscendingWays ∧
    maarijQualityClusters.getLast? = some .rushingDeniersAndPromisedDay := by
  exact ⟨rfl, rfl, rfl⟩

theorem maarij_sat_witness : maarijSat maarijInvariantLedger := by
  unfold maarijSat maarijInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem maarij_gap_witness : maarijGapsExposeBoundary maarijGapLedger := by
  unfold maarijGapsExposeBoundary maarijGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem maarij_access_archaeological :
    maarijSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_al_maarij_sura_quality_witness :
    maarijQualityClusters.length = 5 ∧ maarijSat maarijInvariantLedger ∧
    maarijGapsExposeBoundary maarijGapLedger ∧
    maarijSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : MaarijRegister => MaarijInvariant.ascentDisciplinedRepair)
      MaarijInvariant.ascentDisciplinedRepair := by
  exact ⟨maarij_quality_clusters_shape.left, maarij_sat_witness, maarij_gap_witness,
    maarij_access_archaeological, maarijRegistersAgree⟩

end QuranAlMaarijSuraQualityWitness
end Gnosis.Witnesses.Islam
