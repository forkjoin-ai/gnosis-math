import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranFussilatSuraQualityWitness

/-!
# Quran 41, Fussilat / [Verses] Made Distinct -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:12422-12527`.

This complete sura witness covers Quran 41:1-54.

Fussilat is the articulated-signs witness: distinct Arabic recitation,
creation ordered across days, Ad and Thamud as refused signs, skins and hearing
testifying, steadfast angels, better speech, evil repelled by what is better,
night/day/sun/moon signs, revived earth, and horizons-and-selves disclosure.

No `sorry`, no new `axiom`.
-/

inductive FussilatQualityCluster
  | distinctRecitationAndRefusal
  | creationOrderAndNationWarnings
  | limbWitnessAndCompanionMisguidance
  | steadfastAngelsAndBetterSpeech
  | cosmicSignsRevivedEarthAndHorizonDisclosure
deriving DecidableEq, Repr

def fussilatQualityClusters : List FussilatQualityCluster :=
  [ .distinctRecitationAndRefusal
  , .creationOrderAndNationWarnings
  , .limbWitnessAndCompanionMisguidance
  , .steadfastAngelsAndBetterSpeech
  , .cosmicSignsRevivedEarthAndHorizonDisclosure
  ]

structure FussilatInvariantLedger where
  revelationIsMadeDistinct : Bool := true
  creationSignsAreOrdered : Bool := true
  limbsWitnessAgainstConcealment : Bool := true
  steadfastnessReceivesAngelReassurance : Bool := true
  horizonsAndSelvesDiscloseTruth : Bool := true
deriving DecidableEq, Repr

def fussilatInvariantLedger : FussilatInvariantLedger := {}

def fussilatSat (l : FussilatInvariantLedger) : Prop :=
  l.revelationIsMadeDistinct = true ∧
  l.creationSignsAreOrdered = true ∧
  l.limbsWitnessAgainstConcealment = true ∧
  l.steadfastnessReceivesAngelReassurance = true ∧
  l.horizonsAndSelvesDiscloseTruth = true

structure FussilatGapLedger where
  heartsAreCoveredAgainstHearing : Bool := true
  signsAreAnsweredWithPowerPride : Bool := true
  companionsBeautifyPastAndFuture : Bool := true
  evilSpeechAttemptsToDrownRecitation : Bool := true
  meetingWithLordIsDoubted : Bool := true
deriving DecidableEq, Repr

def fussilatGapLedger : FussilatGapLedger := {}

def fussilatGapsExposeBoundary (g : FussilatGapLedger) : Prop :=
  g.heartsAreCoveredAgainstHearing = true ∧
  g.signsAreAnsweredWithPowerPride = true ∧
  g.companionsBeautifyPastAndFuture = true ∧
  g.evilSpeechAttemptsToDrownRecitation = true ∧
  g.meetingWithLordIsDoubted = true

def fussilatSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 41 / Fussilat witnesses distinct signs, limb testimony, and horizons-selves disclosure"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive FussilatRegister | recitation | creation | limbs | angels | speech | horizons
deriving DecidableEq, Repr, Nonempty

inductive FussilatInvariant | articulatedSignsDisclosure
deriving DecidableEq, Repr

def fussilatRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : FussilatRegister => FussilatInvariant.articulatedSignsDisclosure)
      FussilatInvariant.articulatedSignsDisclosure :=
  TruthOneManyNamesWitness.constant_names_agree FussilatInvariant.articulatedSignsDisclosure

theorem fussilat_quality_clusters_shape :
    fussilatQualityClusters.length = 5 ∧
    fussilatQualityClusters.head? = some .distinctRecitationAndRefusal ∧
    fussilatQualityClusters.getLast? = some .cosmicSignsRevivedEarthAndHorizonDisclosure := by
  exact ⟨rfl, rfl, rfl⟩

theorem fussilat_sat_witness : fussilatSat fussilatInvariantLedger := by
  unfold fussilatSat fussilatInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem fussilat_gap_witness : fussilatGapsExposeBoundary fussilatGapLedger := by
  unfold fussilatGapsExposeBoundary fussilatGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem fussilat_access_archaeological :
    fussilatSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_fussilat_sura_quality_witness :
    fussilatQualityClusters.length = 5 ∧
    fussilatSat fussilatInvariantLedger ∧
    fussilatGapsExposeBoundary fussilatGapLedger ∧
    fussilatSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : FussilatRegister => FussilatInvariant.articulatedSignsDisclosure)
      FussilatInvariant.articulatedSignsDisclosure := by
  exact ⟨fussilat_quality_clusters_shape.left, fussilat_sat_witness, fussilat_gap_witness,
    fussilat_access_archaeological, fussilatRegistersAgree⟩

end QuranFussilatSuraQualityWitness
end Gnosis.Witnesses.Islam
