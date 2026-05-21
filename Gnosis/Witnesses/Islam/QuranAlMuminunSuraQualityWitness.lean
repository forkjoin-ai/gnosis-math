import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlMuminunSuraQualityWitness

/-!
# Quran 23, Al-Mu'minun / The Believers -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:9092-9275`.

This complete sura witness covers Quran 23:1-118.

Al-Mu'minun is the success-and-return witness. Believers succeed through humble
prayer, alms, chastity, trusts, pledges, and prayer-keeping; creation from clay,
measured water, Noah, later messengers, Moses, Mary and Jesus, one community,
truth over desire, sensory gifts, final weighing, and the mercy plea all expose
the return path. The counterproof is arrogance before mortal messengers,
resurrection denial, sectarian rejoicing, wealth-corrupted distress, and late
speech after the barrier.

No `sorry`, no new `axiom`.
-/

inductive AlMuminunQualityCluster
  | successfulBelieversAndEmbryonicCreation
  | measuredWaterLivestockAndNoahArk
  | mortalMessengerDenialAndSuccessiveTales
  | mosesMaryOneCommunityAndTruthRecord
  | desireWouldDisintegrateHeavenAndEarth
  | sensesResurrectionQuestionsAndOneGodProof
  | deathBarrierTrumpetWeightsAndMercyClose
deriving DecidableEq, Repr

def alMuminunQualityClusters : List AlMuminunQualityCluster :=
  [ AlMuminunQualityCluster.successfulBelieversAndEmbryonicCreation
  , AlMuminunQualityCluster.measuredWaterLivestockAndNoahArk
  , AlMuminunQualityCluster.mortalMessengerDenialAndSuccessiveTales
  , AlMuminunQualityCluster.mosesMaryOneCommunityAndTruthRecord
  , AlMuminunQualityCluster.desireWouldDisintegrateHeavenAndEarth
  , AlMuminunQualityCluster.sensesResurrectionQuestionsAndOneGodProof
  , AlMuminunQualityCluster.deathBarrierTrumpetWeightsAndMercyClose
  ]

structure AlMuminunInvariantLedger where
  believerSuccessHasDisciplineShape : Bool := true
  creationStagesWitnessResurrection : Bool := true
  oneCommunityBelongsToOneLord : Bool := true
  recordTellsTruthWithoutOverburdening : Bool := true
  truthCannotFollowDesire : Bool := true
  goodDeedsAreWeighedForSuccess : Bool := true
  mercyIsFinalSupplication : Bool := true
deriving DecidableEq, Repr

def alMuminunInvariantLedger : AlMuminunInvariantLedger := {}

def alMuminunSat (l : AlMuminunInvariantLedger) : Prop :=
  l.believerSuccessHasDisciplineShape = true ∧
  l.creationStagesWitnessResurrection = true ∧
  l.oneCommunityBelongsToOneLord = true ∧
  l.recordTellsTruthWithoutOverburdening = true ∧
  l.truthCannotFollowDesire = true ∧
  l.goodDeedsAreWeighedForSuccess = true ∧
  l.mercyIsFinalSupplication = true

structure AlMuminunGapLedger where
  mortalMessengerContempt : Bool := true
  resurrectionCalledFarFetched : Bool := true
  communitySplitIntoSects : Bool := true
  wealthMistakenForGoodRace : Bool := true
  arrogantMockeryOfMessages : Bool := true
  ancientFablesDismissal : Bool := true
  lateReturnRequestBehindBarrier : Bool := true
  creationCalledVain : Bool := true
deriving DecidableEq, Repr

def alMuminunGapLedger : AlMuminunGapLedger := {}

def alMuminunGapsExposeBoundary (g : AlMuminunGapLedger) : Prop :=
  g.mortalMessengerContempt = true ∧
  g.resurrectionCalledFarFetched = true ∧
  g.communitySplitIntoSects = true ∧
  g.wealthMistakenForGoodRace = true ∧
  g.arrogantMockeryOfMessages = true ∧
  g.ancientFablesDismissal = true ∧
  g.lateReturnRequestBehindBarrier = true ∧
  g.creationCalledVain = true

def alMuminunSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 23 / Al-Mu'minun witnesses disciplined believer success and final return"
    positiveSamples := [1, 2, 3, 4, 5, 6]
    negativeSamples := [7, 8, 9, 10, 11, 12] }

inductive AlMuminunRegister | success | creation | ark | community | truth | senses | mercy
deriving DecidableEq, Repr, Nonempty

inductive AlMuminunInvariant | disciplinedReturnSuccess
deriving DecidableEq, Repr

def alMuminunRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AlMuminunRegister => AlMuminunInvariant.disciplinedReturnSuccess)
      AlMuminunInvariant.disciplinedReturnSuccess :=
  TruthOneManyNamesWitness.constant_names_agree AlMuminunInvariant.disciplinedReturnSuccess

theorem al_muminun_quality_clusters_shape :
    alMuminunQualityClusters.length = 7
    ∧ alMuminunQualityClusters.head? =
      some AlMuminunQualityCluster.successfulBelieversAndEmbryonicCreation
    ∧ alMuminunQualityClusters.getLast? =
      some AlMuminunQualityCluster.deathBarrierTrumpetWeightsAndMercyClose := by
  exact ⟨rfl, rfl, rfl⟩

theorem al_muminun_sat_witness : alMuminunSat alMuminunInvariantLedger := by
  unfold alMuminunSat alMuminunInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem al_muminun_gap_witness : alMuminunGapsExposeBoundary alMuminunGapLedger := by
  unfold alMuminunGapsExposeBoundary alMuminunGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem al_muminun_access_archaeological :
    alMuminunSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_al_muminun_sura_quality_witness :
    alMuminunQualityClusters.length = 7 ∧
    alMuminunSat alMuminunInvariantLedger ∧
    alMuminunGapsExposeBoundary alMuminunGapLedger ∧
    alMuminunSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : AlMuminunRegister => AlMuminunInvariant.disciplinedReturnSuccess)
      AlMuminunInvariant.disciplinedReturnSuccess := by
  exact ⟨al_muminun_quality_clusters_shape.left, al_muminun_sat_witness,
    al_muminun_gap_witness, al_muminun_access_archaeological, alMuminunRegistersAgree⟩

end QuranAlMuminunSuraQualityWitness
end Gnosis.Witnesses.Islam
