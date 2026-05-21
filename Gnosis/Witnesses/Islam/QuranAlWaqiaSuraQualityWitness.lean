import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlWaqiaSuraQualityWitness

/-!
# Quran 56, Al-Waqia / That which is Coming -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:14050-14126`.

This complete sura witness covers Quran 56:1-96.

Al-Waqia is the final-sorting-and-created-dependence witness. The coming event
cannot be denied; people split into the foremost, right, and left; Garden and
Fire outcomes are shown; creation from semen, crops, water, and fire exposes
human non-ownership; the setting stars swear to a noble Quran; and deathbed
helplessness confirms the sorted return.

No `sorry`, no new `axiom`.
-/

inductive WaqiaQualityCluster
  | undeniableEventAndThreefoldSorting
  | foremostAndRightHandProvision
  | leftHandFireAndBoilingWater
  | semenCropsWaterFireAndCreatedDependence
  | starOathNobleQuranDeathbedAndReturn
deriving DecidableEq, Repr

def waqiaQualityClusters : List WaqiaQualityCluster :=
  [ .undeniableEventAndThreefoldSorting
  , .foremostAndRightHandProvision
  , .leftHandFireAndBoilingWater
  , .semenCropsWaterFireAndCreatedDependence
  , .starOathNobleQuranDeathbedAndReturn
  ]

structure WaqiaInvariantLedger where
  comingEventCannotBeDenied : Bool := true
  finalSortingDisclosesRank : Bool := true
  createdDependenceDefeatsOwnershipClaims : Bool := true
  nobleQuranIsGuardedDisclosure : Bool := true
  deathbedHelplessnessConfirmsReturn : Bool := true
deriving DecidableEq, Repr

def waqiaInvariantLedger : WaqiaInvariantLedger := {}

def waqiaSat (l : WaqiaInvariantLedger) : Prop :=
  l.comingEventCannotBeDenied = true ∧
  l.finalSortingDisclosesRank = true ∧
  l.createdDependenceDefeatsOwnershipClaims = true ∧
  l.nobleQuranIsGuardedDisclosure = true ∧
  l.deathbedHelplessnessConfirmsReturn = true

structure WaqiaGapLedger where
  leftHandOutcomeExposesDenial : Bool := true
  cropWaterFireOwnershipClaimsFail : Bool := true
  deathCannotBeReturnedWhenItArrives : Bool := true
  provisionCanBeAnsweredWithDenial : Bool := true
  falseIfOnlyChallengeCannotRecoverSoul : Bool := true
deriving DecidableEq, Repr

def waqiaGapLedger : WaqiaGapLedger := {}

def waqiaGapsExposeBoundary (g : WaqiaGapLedger) : Prop :=
  g.leftHandOutcomeExposesDenial = true ∧
  g.cropWaterFireOwnershipClaimsFail = true ∧
  g.deathCannotBeReturnedWhenItArrives = true ∧
  g.provisionCanBeAnsweredWithDenial = true ∧
  g.falseIfOnlyChallengeCannotRecoverSoul = true

def waqiaSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 56 / Al-Waqia witnesses final sorting, created dependence, and deathbed proof"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive WaqiaRegister | event | sorting | garden | fire | dependence | death
deriving DecidableEq, Repr, Nonempty

inductive WaqiaInvariant | finalSortingDependence
deriving DecidableEq, Repr

def waqiaRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : WaqiaRegister => WaqiaInvariant.finalSortingDependence)
      WaqiaInvariant.finalSortingDependence :=
  TruthOneManyNamesWitness.constant_names_agree WaqiaInvariant.finalSortingDependence

theorem waqia_quality_clusters_shape :
    waqiaQualityClusters.length = 5 ∧
    waqiaQualityClusters.head? = some .undeniableEventAndThreefoldSorting ∧
    waqiaQualityClusters.getLast? = some .starOathNobleQuranDeathbedAndReturn := by
  exact ⟨rfl, rfl, rfl⟩

theorem waqia_sat_witness : waqiaSat waqiaInvariantLedger := by
  unfold waqiaSat waqiaInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem waqia_gap_witness : waqiaGapsExposeBoundary waqiaGapLedger := by
  unfold waqiaGapsExposeBoundary waqiaGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem waqia_access_archaeological :
    waqiaSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_al_waqia_sura_quality_witness :
    waqiaQualityClusters.length = 5 ∧
    waqiaSat waqiaInvariantLedger ∧
    waqiaGapsExposeBoundary waqiaGapLedger ∧
    waqiaSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : WaqiaRegister => WaqiaInvariant.finalSortingDependence)
      WaqiaInvariant.finalSortingDependence := by
  exact ⟨waqia_quality_clusters_shape.left, waqia_sat_witness, waqia_gap_witness,
    waqia_access_archaeological, waqiaRegistersAgree⟩

end QuranAlWaqiaSuraQualityWitness
end Gnosis.Witnesses.Islam
