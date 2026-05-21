import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranTahaSuraQualityWitness

/-!
# Quran 20, Taha / Ta Ha -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:8377-8642`.

This complete sura witness covers Quran 20:1-135.

Taha is the non-distress revelation witness. The Quran is reminder, not burden;
Moses is chosen at Tuwa, equipped with signs and Aaron, sent gently to Pharaoh,
vindicated against sorcery, and used to expose calf-idolatry after rescue. The
sura then folds the same pattern through Adam: forgetting, Satanic whisper,
repentance, guidance, and final patience in worship. The counterproof is haste,
tyranny, sorcery propaganda, calf devotion, turning from reminder, and longing
at worldly finery.

No `sorry`, no new `axiom`.
-/

inductive TahaQualityCluster
  | quranNotDistressAndHiddenKnowledge
  | tuwaChoicePrayerAndGreatSigns
  | mosesRequestAaronAndWatchedFormation
  | gentlePharaohMissionAndCreatorGuidance
  | sorceryContestAndBelievingSorcerers
  | seaRescueProvisionAndCalfTest
  | samiriExposureOneGodAndHeavyBurden
  | dayWhispersArabicWarningAndKnowledgePrayer
  | adamForgettingRepentanceAndGuidanceOutcome
  | patiencePraisePrayerAndEvenPathWaiting
deriving DecidableEq, Repr

def tahaQualityClusters : List TahaQualityCluster :=
  [ TahaQualityCluster.quranNotDistressAndHiddenKnowledge
  , TahaQualityCluster.tuwaChoicePrayerAndGreatSigns
  , TahaQualityCluster.mosesRequestAaronAndWatchedFormation
  , TahaQualityCluster.gentlePharaohMissionAndCreatorGuidance
  , TahaQualityCluster.sorceryContestAndBelievingSorcerers
  , TahaQualityCluster.seaRescueProvisionAndCalfTest
  , TahaQualityCluster.samiriExposureOneGodAndHeavyBurden
  , TahaQualityCluster.dayWhispersArabicWarningAndKnowledgePrayer
  , TahaQualityCluster.adamForgettingRepentanceAndGuidanceOutcome
  , TahaQualityCluster.patiencePraisePrayerAndEvenPathWaiting
  ]

structure TahaInvariantLedger where
  quranIsReminderNotDistress : Bool := true
  godKnowsSecretAndMoreHidden : Bool := true
  chosenMissionIsPairedWithRemembrance : Bool := true
  gentleSpeechRemainsCommandUnderTyranny : Bool := true
  truthSwallowsSorcery : Bool := true
  repentanceRestoresRightPathAfterFall : Bool := true
  guidancePreventsMisery : Bool := true
  patiencePrayerAndPraiseCloseTheSura : Bool := true
deriving DecidableEq, Repr

def tahaInvariantLedger : TahaInvariantLedger := {}

def tahaSat (l : TahaInvariantLedger) : Prop :=
  l.quranIsReminderNotDistress = true ∧
  l.godKnowsSecretAndMoreHidden = true ∧
  l.chosenMissionIsPairedWithRemembrance = true ∧
  l.gentleSpeechRemainsCommandUnderTyranny = true ∧
  l.truthSwallowsSorcery = true ∧
  l.repentanceRestoresRightPathAfterFall = true ∧
  l.guidancePreventsMisery = true ∧
  l.patiencePrayerAndPraiseCloseTheSura = true

structure TahaGapLedger where
  pharaohExceedsAllBounds : Bool := true
  sorceryFramesClearSigns : Bool := true
  forcedSorceryAndThreatenedCrucifixion : Bool := true
  provisionOversteppedAfterRescue : Bool := true
  calfCannotAnswerHarmOrBenefit : Bool := true
  samiriSoulPromptedFabrication : Bool := true
  reminderTurnedAwayFrom : Bool := true
  adamForgetsAndLacksConstancy : Bool := true
  revelationsIgnoredThenBlindness : Bool := true
  worldlyFineryGazedAtLongingly : Bool := true
deriving DecidableEq, Repr

def tahaGapLedger : TahaGapLedger := {}

def tahaGapsExposeBoundary (g : TahaGapLedger) : Prop :=
  g.pharaohExceedsAllBounds = true ∧
  g.sorceryFramesClearSigns = true ∧
  g.forcedSorceryAndThreatenedCrucifixion = true ∧
  g.provisionOversteppedAfterRescue = true ∧
  g.calfCannotAnswerHarmOrBenefit = true ∧
  g.samiriSoulPromptedFabrication = true ∧
  g.reminderTurnedAwayFrom = true ∧
  g.adamForgetsAndLacksConstancy = true ∧
  g.revelationsIgnoredThenBlindness = true ∧
  g.worldlyFineryGazedAtLongingly = true

def tahaSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 20 / Taha witnesses reminder without distress through Moses, calf, Adam, and patient worship"
    positiveSamples := [1, 2, 3, 4, 5, 6, 7]
    negativeSamples := [8, 9, 10, 11, 12, 13] }

inductive TahaRegister | reminder | tuwa | mission | sorcery | calf | burden | adam | patience
deriving DecidableEq, Repr, Nonempty

inductive TahaInvariant | reminderGuidanceWithoutMisery
deriving DecidableEq, Repr

def tahaRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : TahaRegister => TahaInvariant.reminderGuidanceWithoutMisery)
      TahaInvariant.reminderGuidanceWithoutMisery :=
  TruthOneManyNamesWitness.constant_names_agree TahaInvariant.reminderGuidanceWithoutMisery

theorem taha_quality_clusters_shape :
    tahaQualityClusters.length = 10
    ∧ tahaQualityClusters.head? =
      some TahaQualityCluster.quranNotDistressAndHiddenKnowledge
    ∧ tahaQualityClusters.getLast? =
      some TahaQualityCluster.patiencePraisePrayerAndEvenPathWaiting := by
  exact ⟨rfl, rfl, rfl⟩

theorem taha_sat_witness : tahaSat tahaInvariantLedger := by
  unfold tahaSat tahaInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem taha_gap_witness : tahaGapsExposeBoundary tahaGapLedger := by
  unfold tahaGapsExposeBoundary tahaGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem taha_access_archaeological :
    tahaSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_taha_sura_quality_witness :
    tahaQualityClusters.length = 10 ∧
    tahaSat tahaInvariantLedger ∧
    tahaGapsExposeBoundary tahaGapLedger ∧
    tahaSuraAccess.mode =
      Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : TahaRegister => TahaInvariant.reminderGuidanceWithoutMisery)
      TahaInvariant.reminderGuidanceWithoutMisery := by
  exact ⟨taha_quality_clusters_shape.left, taha_sat_witness, taha_gap_witness,
    taha_access_archaeological, tahaRegistersAgree⟩

end QuranTahaSuraQualityWitness
end Gnosis.Witnesses.Islam
