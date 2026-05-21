import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAnNajmSuraQualityWitness

/-!
# Quran 53, An-Najm / The Star -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:13764-13841`.

This complete sura witness covers Quran 53:1-62.

An-Najm is the vision-and-proportion witness. The setting star swears that the
Prophet has not strayed; revelation is taught by a mighty one; the Lote Tree
vision is not overreached; goddesses and angel-daughter claims are exposed as
names without authority; desire cannot replace truth; every soul bears its own
earning; and Abraham and Moses' scroll logic returns accountability to God.

No `sorry`, no new `axiom`.
-/

inductive NajmQualityCluster
  | starOathAndUnstrayedCompanion
  | mightyTeacherNearHorizonAndLoteTreeVision
  | namedGoddessesAngelClaimsAndDesireBoundary
  | soulEarningAndNoBurdenTransfer
  | abrahamMosesScrollsAndFinalReturn
deriving DecidableEq, Repr

def najmQualityClusters : List NajmQualityCluster :=
  [ .starOathAndUnstrayedCompanion
  , .mightyTeacherNearHorizonAndLoteTreeVision
  , .namedGoddessesAngelClaimsAndDesireBoundary
  , .soulEarningAndNoBurdenTransfer
  , .abrahamMosesScrollsAndFinalReturn
  ]

structure NajmInvariantLedger where
  revelationIsNotStrayingOrDesire : Bool := true
  visionStaysWithinItsLimit : Bool := true
  namesWithoutAuthorityDoNotBindTruth : Bool := true
  eachSoulOwnsItsEarning : Bool := true
  finalReturnBelongsToGod : Bool := true
deriving DecidableEq, Repr

def najmInvariantLedger : NajmInvariantLedger := {}

def najmSat (l : NajmInvariantLedger) : Prop :=
  l.revelationIsNotStrayingOrDesire = true ∧
  l.visionStaysWithinItsLimit = true ∧
  l.namesWithoutAuthorityDoNotBindTruth = true ∧
  l.eachSoulOwnsItsEarning = true ∧
  l.finalReturnBelongsToGod = true

structure NajmGapLedger where
  desireSubstitutesForGuidance : Bool := true
  feminineAngelClaimProjectsWithoutKnowledge : Bool := true
  partialGivingThenWithholdingExposesThinFaith : Bool := true
  burdenTransferFantasyFails : Bool := true
  amusementAtWarningBlocksProstration : Bool := true
deriving DecidableEq, Repr

def najmGapLedger : NajmGapLedger := {}

def najmGapsExposeBoundary (g : NajmGapLedger) : Prop :=
  g.desireSubstitutesForGuidance = true ∧
  g.feminineAngelClaimProjectsWithoutKnowledge = true ∧
  g.partialGivingThenWithholdingExposesThinFaith = true ∧
  g.burdenTransferFantasyFails = true ∧
  g.amusementAtWarningBlocksProstration = true

def najmSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 53 / An-Najm witnesses bounded vision, desire's failure, and earned return"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive NajmRegister | star | vision | names | desire | scrolls | return
deriving DecidableEq, Repr, Nonempty

inductive NajmInvariant | boundedVisionEarnedReturn
deriving DecidableEq, Repr

def najmRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : NajmRegister => NajmInvariant.boundedVisionEarnedReturn)
      NajmInvariant.boundedVisionEarnedReturn :=
  TruthOneManyNamesWitness.constant_names_agree NajmInvariant.boundedVisionEarnedReturn

theorem najm_quality_clusters_shape :
    najmQualityClusters.length = 5 ∧
    najmQualityClusters.head? = some .starOathAndUnstrayedCompanion ∧
    najmQualityClusters.getLast? = some .abrahamMosesScrollsAndFinalReturn := by
  exact ⟨rfl, rfl, rfl⟩

theorem najm_sat_witness : najmSat najmInvariantLedger := by
  unfold najmSat najmInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem najm_gap_witness : najmGapsExposeBoundary najmGapLedger := by
  unfold najmGapsExposeBoundary najmGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem najm_access_archaeological :
    najmSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_an_najm_sura_quality_witness :
    najmQualityClusters.length = 5 ∧
    najmSat najmInvariantLedger ∧
    najmGapsExposeBoundary najmGapLedger ∧
    najmSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : NajmRegister => NajmInvariant.boundedVisionEarnedReturn)
      NajmInvariant.boundedVisionEarnedReturn := by
  exact ⟨najm_quality_clusters_shape.left, najm_sat_witness, najm_gap_witness,
    najm_access_archaeological, najmRegistersAgree⟩

end QuranAnNajmSuraQualityWitness
end Gnosis.Witnesses.Islam
