import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlAnkabutSuraQualityWitness

/-!
# Quran 29, Al-Ankabut / The Spider -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:10429-10609`.

This complete sura witness covers Quran 29:1-69.

Al-Ankabut is the tested-faith and frail-house witness. Belief is marked out by
trial; Noah, Abraham, Lot, Shu'ayb, Ad, Thamud, Qarun, Pharaoh, and Haman
expose old denial patterns; the spider house names false protection; prayer
restrains indecency; Scripture suffices; the earth is vast; sea-sincerity
collapses on land; and those who strive are guided to God's ways.

No `sorry`, no new `axiom`.
-/

inductive AlAnkabutQualityCluster
  | beliefTestParentsAndBurdenBoundary
  | noahAbrahamFireLotAndDestroyedTowns
  | shuaybAdThamudQarunPharaohAndSpiderHouse
  | recitationPrayerBookPeopleAndSufficientScripture
  | vastEarthDeathProvisionSeaAndStrivingGuidance
deriving DecidableEq, Repr

def alAnkabutQualityClusters : List AlAnkabutQualityCluster :=
  [ AlAnkabutQualityCluster.beliefTestParentsAndBurdenBoundary
  , AlAnkabutQualityCluster.noahAbrahamFireLotAndDestroyedTowns
  , AlAnkabutQualityCluster.shuaybAdThamudQarunPharaohAndSpiderHouse
  , AlAnkabutQualityCluster.recitationPrayerBookPeopleAndSufficientScripture
  , AlAnkabutQualityCluster.vastEarthDeathProvisionSeaAndStrivingGuidance
  ]

structure AlAnkabutInvariantLedger where
  beliefMustBeTested : Bool := true
  strivingBenefitsTheStriver : Bool := true
  godSavesBelievingRemnants : Bool := true
  falseProtectorsAreSpiderHouses : Bool := true
  prayerRestrainsIndecency : Bool := true
  scriptureRecitationIsSufficientMercy : Bool := true
  striversAreGuidedToGodsWays : Bool := true
deriving DecidableEq, Repr

def alAnkabutInvariantLedger : AlAnkabutInvariantLedger := {}

def alAnkabutSat (l : AlAnkabutInvariantLedger) : Prop :=
  l.beliefMustBeTested = true ∧
  l.strivingBenefitsTheStriver = true ∧
  l.godSavesBelievingRemnants = true ∧
  l.falseProtectorsAreSpiderHouses = true ∧
  l.prayerRestrainsIndecency = true ∧
  l.scriptureRecitationIsSufficientMercy = true ∧
  l.striversAreGuidedToGodsWays = true

structure AlAnkabutGapLedger where
  persecutionEquatedWithGodsPunishment : Bool := true
  disbelieversOfferToCarrySins : Bool := true
  idolsInventedAsFalsehood : Bool := true
  outrageousActsAndCorruption : Bool := true
  satanMadeFoulDeedsAlluring : Bool := true
  miraclesDemandedAgainstPlainWarning : Bool := true
  punishmentHastened : Bool := true
  seaSincerityTurnsToShirkOnLand : Bool := true
deriving DecidableEq, Repr

def alAnkabutGapLedger : AlAnkabutGapLedger := {}

def alAnkabutGapsExposeBoundary (g : AlAnkabutGapLedger) : Prop :=
  g.persecutionEquatedWithGodsPunishment = true ∧
  g.disbelieversOfferToCarrySins = true ∧
  g.idolsInventedAsFalsehood = true ∧
  g.outrageousActsAndCorruption = true ∧
  g.satanMadeFoulDeedsAlluring = true ∧
  g.miraclesDemandedAgainstPlainWarning = true ∧
  g.punishmentHastened = true ∧
  g.seaSincerityTurnsToShirkOnLand = true

def alAnkabutSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 29 / Al-Ankabut witnesses tested faith and the frailty of false shelters"
    positiveSamples := [1, 2, 3, 4, 5, 6]
    negativeSamples := [7, 8, 9, 10, 11, 12] }

inductive AlAnkabutRegister | test | prophets | spider | prayer | scripture | earth | striving
deriving DecidableEq, Repr, Nonempty

inductive AlAnkabutInvariant | testedFaithTrueShelter
deriving DecidableEq, Repr

def alAnkabutRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AlAnkabutRegister => AlAnkabutInvariant.testedFaithTrueShelter)
      AlAnkabutInvariant.testedFaithTrueShelter :=
  TruthOneManyNamesWitness.constant_names_agree AlAnkabutInvariant.testedFaithTrueShelter

theorem al_ankabut_quality_clusters_shape :
    alAnkabutQualityClusters.length = 5
    ∧ alAnkabutQualityClusters.head? =
      some AlAnkabutQualityCluster.beliefTestParentsAndBurdenBoundary
    ∧ alAnkabutQualityClusters.getLast? =
      some AlAnkabutQualityCluster.vastEarthDeathProvisionSeaAndStrivingGuidance := by
  exact ⟨rfl, rfl, rfl⟩

theorem al_ankabut_sat_witness : alAnkabutSat alAnkabutInvariantLedger := by
  unfold alAnkabutSat alAnkabutInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem al_ankabut_gap_witness : alAnkabutGapsExposeBoundary alAnkabutGapLedger := by
  unfold alAnkabutGapsExposeBoundary alAnkabutGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem al_ankabut_access_archaeological :
    alAnkabutSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_al_ankabut_sura_quality_witness :
    alAnkabutQualityClusters.length = 5 ∧
    alAnkabutSat alAnkabutInvariantLedger ∧
    alAnkabutGapsExposeBoundary alAnkabutGapLedger ∧
    alAnkabutSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AlAnkabutRegister => AlAnkabutInvariant.testedFaithTrueShelter)
      AlAnkabutInvariant.testedFaithTrueShelter := by
  exact ⟨al_ankabut_quality_clusters_shape.left, al_ankabut_sat_witness,
    al_ankabut_gap_witness, al_ankabut_access_archaeological, alAnkabutRegistersAgree⟩

end QuranAlAnkabutSuraQualityWitness
end Gnosis.Witnesses.Islam
