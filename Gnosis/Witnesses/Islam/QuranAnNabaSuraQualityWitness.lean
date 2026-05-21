import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAnNabaSuraQualityWitness

/-! # Quran 78, An-Naba / The Announcement -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:15485-15521`.
This witness covers Quran 78:1-40: the momentous announcement, earth/sky/night
signs, sent-down water, Day of Decision, Hell as ambush, Garden as reward, and
the warning that humans will see what their hands sent ahead. No `sorry`, no new `axiom`. -/

inductive NabaQualityCluster
  | announcementDisputeAndSoonKnowing | earthSkyNightDayAndRainSigns
  | decisionDayTrumpetAndOpenedSky | hellAmbushAndExactRecompense
  | gardenRewardSpiritRowsAndSentAheadWarning
deriving DecidableEq, Repr
def nabaQualityClusters : List NabaQualityCluster :=
  [ .announcementDisputeAndSoonKnowing, .earthSkyNightDayAndRainSigns, .decisionDayTrumpetAndOpenedSky,
    .hellAmbushAndExactRecompense, .gardenRewardSpiritRowsAndSentAheadWarning ]

structure NabaInvariantLedger where
  announcementWillBeKnown : Bool := true
  creationSignsGroundDecision : Bool := true
  recompenseIsExact : Bool := true
  mindfulReceiveMeasuredReward : Bool := true
  sentAheadDeedsBecomeVisible : Bool := true
deriving DecidableEq, Repr
def nabaInvariantLedger : NabaInvariantLedger := {}
def nabaSat (l : NabaInvariantLedger) : Prop :=
  l.announcementWillBeKnown = true ∧ l.creationSignsGroundDecision = true ∧
  l.recompenseIsExact = true ∧ l.mindfulReceiveMeasuredReward = true ∧
  l.sentAheadDeedsBecomeVisible = true

structure NabaGapLedger where
  announcementIsDisputed : Bool := true
  accountIsNotExpected : Bool := true
  signsAreDeniedAsLies : Bool := true
  hellWaitsAsAmbush : Bool := true
  dustWishArrivesTooLate : Bool := true
deriving DecidableEq, Repr
def nabaGapLedger : NabaGapLedger := {}
def nabaGapsExposeBoundary (g : NabaGapLedger) : Prop :=
  g.announcementIsDisputed = true ∧ g.accountIsNotExpected = true ∧ g.signsAreDeniedAsLies = true ∧
  g.hellWaitsAsAmbush = true ∧ g.dustWishArrivesTooLate = true
def nabaSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 78 / An-Naba witnesses the announcement, creation signs, exact recompense, and sent-ahead deeds"
    positiveSamples := [1, 2, 3, 4, 5], negativeSamples := [6, 7, 8, 9, 10] }
inductive NabaRegister | announcement | signs | trumpet | hell | garden | deeds
deriving DecidableEq, Repr, Nonempty
inductive NabaInvariant | announcementExactDecision deriving DecidableEq, Repr
def nabaRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : NabaRegister => NabaInvariant.announcementExactDecision)
      NabaInvariant.announcementExactDecision :=
  TruthOneManyNamesWitness.constant_names_agree NabaInvariant.announcementExactDecision
theorem naba_quality_clusters_shape :
    nabaQualityClusters.length = 5 ∧ nabaQualityClusters.head? = some .announcementDisputeAndSoonKnowing ∧
    nabaQualityClusters.getLast? = some .gardenRewardSpiritRowsAndSentAheadWarning := by exact ⟨rfl, rfl, rfl⟩
theorem naba_sat_witness : nabaSat nabaInvariantLedger := by
  unfold nabaSat nabaInvariantLedger; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem naba_gap_witness : nabaGapsExposeBoundary nabaGapLedger := by
  unfold nabaGapsExposeBoundary nabaGapLedger; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem naba_access_archaeological :
    nabaSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by rfl
theorem quran_an_naba_sura_quality_witness :
    nabaQualityClusters.length = 5 ∧ nabaSat nabaInvariantLedger ∧ nabaGapsExposeBoundary nabaGapLedger ∧
    nabaSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : NabaRegister => NabaInvariant.announcementExactDecision)
      NabaInvariant.announcementExactDecision := by
  exact ⟨naba_quality_clusters_shape.left, naba_sat_witness, naba_gap_witness,
    naba_access_archaeological, nabaRegistersAgree⟩

end QuranAnNabaSuraQualityWitness
end Gnosis.Witnesses.Islam
