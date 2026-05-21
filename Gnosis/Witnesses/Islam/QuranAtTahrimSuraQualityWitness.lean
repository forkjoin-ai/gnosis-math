import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAtTahrimSuraQualityWitness

/-!
# Quran 66, At-Tahrim / Prohibition -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:14788-14824`.

This complete sura witness covers Quran 66:1-12.

At-Tahrim is the household-secret-and-example witness. Lawful things must not be
self-prohibited to appease others, disclosed secrets expose household pressure,
believers are told to protect themselves and families from Fire, sincere
repentance is opened, and Noah's wife, Lot's wife, Pharaoh's wife, and Mary form
paired negative and positive examples.

No `sorry`, no new `axiom`.
-/

inductive TahrimQualityCluster
  | lawfulProhibitionAndOathRelease
  | householdSecretDisclosureAndSupport
  | familyFireProtectionAndSincereRepentance
  | noahLotWivesNegativeExamples
  | pharaohWifeMaryAndFaithfulEmbodiment
deriving DecidableEq, Repr

def tahrimQualityClusters : List TahrimQualityCluster :=
  [ .lawfulProhibitionAndOathRelease, .householdSecretDisclosureAndSupport,
    .familyFireProtectionAndSincereRepentance, .noahLotWivesNegativeExamples,
    .pharaohWifeMaryAndFaithfulEmbodiment ]

structure TahrimInvariantLedger where
  lawfulMercyOutranksAppeasementProhibition : Bool := true
  hiddenHouseholdSpeechCanBeDisclosed : Bool := true
  repentanceCanRepairBeforeFire : Bool := true
  kinshipDoesNotSaveBetrayal : Bool := true
  faithfulExampleCanStandInsideHostileHouse : Bool := true
deriving DecidableEq, Repr

def tahrimInvariantLedger : TahrimInvariantLedger := {}

def tahrimSat (l : TahrimInvariantLedger) : Prop :=
  l.lawfulMercyOutranksAppeasementProhibition = true ∧ l.hiddenHouseholdSpeechCanBeDisclosed = true ∧
  l.repentanceCanRepairBeforeFire = true ∧ l.kinshipDoesNotSaveBetrayal = true ∧
  l.faithfulExampleCanStandInsideHostileHouse = true

structure TahrimGapLedger where
  appeasementCanMisstateLawfulMercy : Bool := true
  householdCollusionCanPressureMessenger : Bool := true
  familyNeglectLeavesFireBoundaryOpen : Bool := true
  propheticKinshipCannotSaveTreacherousWives : Bool := true
  hostilePowerCannotContainFaithfulRefuge : Bool := true
deriving DecidableEq, Repr

def tahrimGapLedger : TahrimGapLedger := {}

def tahrimGapsExposeBoundary (g : TahrimGapLedger) : Prop :=
  g.appeasementCanMisstateLawfulMercy = true ∧ g.householdCollusionCanPressureMessenger = true ∧
  g.familyNeglectLeavesFireBoundaryOpen = true ∧ g.propheticKinshipCannotSaveTreacherousWives = true ∧
  g.hostilePowerCannotContainFaithfulRefuge = true

def tahrimSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 66 / At-Tahrim witnesses lawful mercy, household disclosure, repentance, and examples"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive TahrimRegister | lawful | secret | family | repentance | wives | mary
deriving DecidableEq, Repr, Nonempty

inductive TahrimInvariant | householdRepairExamples
deriving DecidableEq, Repr

def tahrimRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : TahrimRegister => TahrimInvariant.householdRepairExamples)
      TahrimInvariant.householdRepairExamples :=
  TruthOneManyNamesWitness.constant_names_agree TahrimInvariant.householdRepairExamples

theorem tahrim_quality_clusters_shape :
    tahrimQualityClusters.length = 5 ∧ tahrimQualityClusters.head? = some .lawfulProhibitionAndOathRelease ∧
    tahrimQualityClusters.getLast? = some .pharaohWifeMaryAndFaithfulEmbodiment := by
  exact ⟨rfl, rfl, rfl⟩

theorem tahrim_sat_witness : tahrimSat tahrimInvariantLedger := by
  unfold tahrimSat tahrimInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem tahrim_gap_witness : tahrimGapsExposeBoundary tahrimGapLedger := by
  unfold tahrimGapsExposeBoundary tahrimGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem tahrim_access_archaeological :
    tahrimSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_at_tahrim_sura_quality_witness :
    tahrimQualityClusters.length = 5 ∧ tahrimSat tahrimInvariantLedger ∧
    tahrimGapsExposeBoundary tahrimGapLedger ∧
    tahrimSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : TahrimRegister => TahrimInvariant.householdRepairExamples)
      TahrimInvariant.householdRepairExamples := by
  exact ⟨tahrim_quality_clusters_shape.left, tahrim_sat_witness, tahrim_gap_witness,
    tahrim_access_archaeological, tahrimRegistersAgree⟩

end QuranAtTahrimSuraQualityWitness
end Gnosis.Witnesses.Islam
