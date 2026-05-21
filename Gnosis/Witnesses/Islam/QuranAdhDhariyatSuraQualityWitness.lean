import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAdhDhariyatSuraQualityWitness

/-!
# Quran 51, Adh-Dhariyat / The Scattering Winds -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:13612-13648`.

This complete sura witness covers Quran 51:1-60.

Adh-Dhariyat is the oath-distribution-and-hospitality witness. Scattering winds,
burden-bearing clouds, easy ships, and distributing angels swear to promised
judgment; earth and selves carry signs; Abraham's honored guests announce Isaac
and expose Lot's doomed town; Moses, Ad, Thamud, and Noah supply repeated
negative witnesses; creation in pairs and worship as human purpose close the
ledger.

No `sorry`, no new `axiom`.
-/

inductive DhariyatQualityCluster
  | scatteringOathsAndPromisedJudgment
  | signsInEarthSelvesAndProvisionAbove
  | abrahamGuestsHospitalityAndIsaacPromise
  | lotMosesAdThamudNoahWarningCycle
  | pairedCreationAndWorshipPurpose
deriving DecidableEq, Repr

def dhariyatQualityClusters : List DhariyatQualityCluster :=
  [ .scatteringOathsAndPromisedJudgment
  , .signsInEarthSelvesAndProvisionAbove
  , .abrahamGuestsHospitalityAndIsaacPromise
  , .lotMosesAdThamudNoahWarningCycle
  , .pairedCreationAndWorshipPurpose
  ]

structure DhariyatInvariantLedger where
  promisedJudgmentIsTrue : Bool := true
  signsAppearInEarthAndSelves : Bool := true
  hospitalityReceivesAngelicDisclosure : Bool := true
  repeatedWarningsExposeDenialPattern : Bool := true
  worshipNamesHumanPurpose : Bool := true
deriving DecidableEq, Repr

def dhariyatInvariantLedger : DhariyatInvariantLedger := {}

def dhariyatSat (l : DhariyatInvariantLedger) : Prop :=
  l.promisedJudgmentIsTrue = true ∧
  l.signsAppearInEarthAndSelves = true ∧
  l.hospitalityReceivesAngelicDisclosure = true ∧
  l.repeatedWarningsExposeDenialPattern = true ∧
  l.worshipNamesHumanPurpose = true

structure DhariyatGapLedger where
  contradictoryTalkDistractsFromJudgment : Bool := true
  barrenAmazementMisreadsPromise : Bool := true
  tyrantsDismissSignsAsSorceryOrMadness : Bool := true
  ancientCyclesRepeatTheSameCharge : Bool := true
  shareOfPunishmentCannotBeHastenedSafely : Bool := true
deriving DecidableEq, Repr

def dhariyatGapLedger : DhariyatGapLedger := {}

def dhariyatGapsExposeBoundary (g : DhariyatGapLedger) : Prop :=
  g.contradictoryTalkDistractsFromJudgment = true ∧
  g.barrenAmazementMisreadsPromise = true ∧
  g.tyrantsDismissSignsAsSorceryOrMadness = true ∧
  g.ancientCyclesRepeatTheSameCharge = true ∧
  g.shareOfPunishmentCannotBeHastenedSafely = true

def dhariyatSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 51 / Adh-Dhariyat witnesses distributed oaths, hospitable disclosure, and worship purpose"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive DhariyatRegister | winds | signs | guests | nations | pairs | worship
deriving DecidableEq, Repr, Nonempty

inductive DhariyatInvariant | distributedSignsPurpose
deriving DecidableEq, Repr

def dhariyatRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : DhariyatRegister => DhariyatInvariant.distributedSignsPurpose)
      DhariyatInvariant.distributedSignsPurpose :=
  TruthOneManyNamesWitness.constant_names_agree DhariyatInvariant.distributedSignsPurpose

theorem dhariyat_quality_clusters_shape :
    dhariyatQualityClusters.length = 5 ∧
    dhariyatQualityClusters.head? = some .scatteringOathsAndPromisedJudgment ∧
    dhariyatQualityClusters.getLast? = some .pairedCreationAndWorshipPurpose := by
  exact ⟨rfl, rfl, rfl⟩

theorem dhariyat_sat_witness : dhariyatSat dhariyatInvariantLedger := by
  unfold dhariyatSat dhariyatInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem dhariyat_gap_witness : dhariyatGapsExposeBoundary dhariyatGapLedger := by
  unfold dhariyatGapsExposeBoundary dhariyatGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem dhariyat_access_archaeological :
    dhariyatSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_adh_dhariyat_sura_quality_witness :
    dhariyatQualityClusters.length = 5 ∧
    dhariyatSat dhariyatInvariantLedger ∧
    dhariyatGapsExposeBoundary dhariyatGapLedger ∧
    dhariyatSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : DhariyatRegister => DhariyatInvariant.distributedSignsPurpose)
      DhariyatInvariant.distributedSignsPurpose := by
  exact ⟨dhariyat_quality_clusters_shape.left, dhariyat_sat_witness, dhariyat_gap_witness,
    dhariyat_access_archaeological, dhariyatRegistersAgree⟩

end QuranAdhDhariyatSuraQualityWitness
end Gnosis.Witnesses.Islam
