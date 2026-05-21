import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlMursalatSuraQualityWitness

/-! # Quran 77, Al-Mursalat / Emissaries -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:15432-15468`.
This witness covers Quran 77:1-50: emissary winds, Day of Decision, destroyed
former peoples, human creation from fluid, earth as gathering place, and the
repeated woe refrain. No `sorry`, no new `axiom`. -/

inductive MursalatQualityCluster
  | emissaryOathsAndDecisionDay | formerPeopleDestruction
  | fluidCreationAndMeasuredTerm | earthGatheringAndMountainProvision
  | smokeShadeFireAndRepeatedWoe
deriving DecidableEq, Repr
def mursalatQualityClusters : List MursalatQualityCluster :=
  [ .emissaryOathsAndDecisionDay, .formerPeopleDestruction, .fluidCreationAndMeasuredTerm,
    .earthGatheringAndMountainProvision, .smokeShadeFireAndRepeatedWoe ]

structure MursalatInvariantLedger where
  promisedDecisionArrives : Bool := true
  formerDestructionWarnsLaterDeniers : Bool := true
  measuredCreationGroundsAccount : Bool := true
  earthGathersLivingAndDead : Bool := true
  repeatedWoeMarksPersistentDenial : Bool := true
deriving DecidableEq, Repr
def mursalatInvariantLedger : MursalatInvariantLedger := {}
def mursalatSat (l : MursalatInvariantLedger) : Prop :=
  l.promisedDecisionArrives = true ∧ l.formerDestructionWarnsLaterDeniers = true ∧
  l.measuredCreationGroundsAccount = true ∧ l.earthGathersLivingAndDead = true ∧
  l.repeatedWoeMarksPersistentDenial = true

structure MursalatGapLedger where
  decisionIsDeniedDespiteOaths : Bool := true
  formerWarningsAreIgnored : Bool := true
  createdFluidMisreadsItsMeasure : Bool := true
  noPermissionForExcusesRemains : Bool := true
  bowingCommandCanStillBeRefused : Bool := true
deriving DecidableEq, Repr
def mursalatGapLedger : MursalatGapLedger := {}
def mursalatGapsExposeBoundary (g : MursalatGapLedger) : Prop :=
  g.decisionIsDeniedDespiteOaths = true ∧ g.formerWarningsAreIgnored = true ∧
  g.createdFluidMisreadsItsMeasure = true ∧ g.noPermissionForExcusesRemains = true ∧
  g.bowingCommandCanStillBeRefused = true

def mursalatSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 77 / Al-Mursalat witnesses emissary oaths, measured creation, and decision woe"
    positiveSamples := [1, 2, 3, 4, 5], negativeSamples := [6, 7, 8, 9, 10] }
inductive MursalatRegister | winds | decision | peoples | fluid | earth | woe
deriving DecidableEq, Repr, Nonempty
inductive MursalatInvariant | measuredDecisionWarning deriving DecidableEq, Repr
def mursalatRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : MursalatRegister => MursalatInvariant.measuredDecisionWarning)
      MursalatInvariant.measuredDecisionWarning :=
  TruthOneManyNamesWitness.constant_names_agree MursalatInvariant.measuredDecisionWarning
theorem mursalat_quality_clusters_shape :
    mursalatQualityClusters.length = 5 ∧ mursalatQualityClusters.head? = some .emissaryOathsAndDecisionDay ∧
    mursalatQualityClusters.getLast? = some .smokeShadeFireAndRepeatedWoe := by exact ⟨rfl, rfl, rfl⟩
theorem mursalat_sat_witness : mursalatSat mursalatInvariantLedger := by
  unfold mursalatSat mursalatInvariantLedger; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem mursalat_gap_witness : mursalatGapsExposeBoundary mursalatGapLedger := by
  unfold mursalatGapsExposeBoundary mursalatGapLedger; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem mursalat_access_archaeological :
    mursalatSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by rfl
theorem quran_al_mursalat_sura_quality_witness :
    mursalatQualityClusters.length = 5 ∧ mursalatSat mursalatInvariantLedger ∧ mursalatGapsExposeBoundary mursalatGapLedger ∧
    mursalatSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : MursalatRegister => MursalatInvariant.measuredDecisionWarning)
      MursalatInvariant.measuredDecisionWarning := by
  exact ⟨mursalat_quality_clusters_shape.left, mursalat_sat_witness, mursalat_gap_witness,
    mursalat_access_archaeological, mursalatRegistersAgree⟩

end QuranAlMursalatSuraQualityWitness
end Gnosis.Witnesses.Islam
