import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraTranscendenceGuidanceWitness

/-!
# Quran 2:116-121, Al-Baqara -- Transcendence, Signs, Guidance

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1325-1341`.

This bounded witness tracks the transcendence and guidance-warning unit:

  * the claim that God has a child is rejected by divine exaltation;
  * everything in the heavens and earth belongs to Him and obeys His will;
  * God originates heaven and earth and decrees by "Be";
  * unknowledged sign-demands repeat earlier patterns of alike hearts;
  * signs are clear for those with solid faith;
  * the Prophet is sent with truth, good news, and warning;
  * communal approval is not the measure of guidance;
  * following desires after knowledge leaves no protector or helper;
  * worthy Scripture-following marks true belief, while denial loses.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive TranscendenceGuidanceMoment
  | childClaimRejected
  | allBelongsAndObeys
  | originatorBeCommand
  | signDemandRepeated
  | signsClearToFaith
  | prophetTruthNewsWarning
  | guidanceOnlyGods
  | desiresAfterKnowledgeWarning
  | scriptureFollowedOrDenied
deriving DecidableEq, Repr

def transcendenceGuidanceMoments : List TranscendenceGuidanceMoment :=
  [ TranscendenceGuidanceMoment.childClaimRejected
  , TranscendenceGuidanceMoment.allBelongsAndObeys
  , TranscendenceGuidanceMoment.originatorBeCommand
  , TranscendenceGuidanceMoment.signDemandRepeated
  , TranscendenceGuidanceMoment.signsClearToFaith
  , TranscendenceGuidanceMoment.prophetTruthNewsWarning
  , TranscendenceGuidanceMoment.guidanceOnlyGods
  , TranscendenceGuidanceMoment.desiresAfterKnowledgeWarning
  , TranscendenceGuidanceMoment.scriptureFollowedOrDenied
  ]

structure TranscendencePattern where
  childClaimAsserted : Bool
  childClaimRejected : Bool
  godExalted : Bool
  heavensEarthBelongToGod : Bool
  allDevoutlyObey : Bool
  originatorHeavensEarth : Bool
  beCommandEffective : Bool
deriving DecidableEq, Repr

def transcendencePattern : TranscendencePattern where
  childClaimAsserted := true
  childClaimRejected := true
  godExalted := true
  heavensEarthBelongToGod := true
  allDevoutlyObey := true
  originatorHeavensEarth := true
  beCommandEffective := true

structure SignsProphetPattern where
  unknowledgedSpeechDemand : Bool
  miraculousSignDemand : Bool
  earlierPeopleSaidSame : Bool
  heartsAlike : Bool
  signsClear : Bool
  solidFaithReceivesSigns : Bool
  prophetSentWithTruth : Bool
  goodNewsBearing : Bool
  warningBearing : Bool
  notResponsibleForBlazePeople : Bool
deriving DecidableEq, Repr

def signsProphetPattern : SignsProphetPattern where
  unknowledgedSpeechDemand := true
  miraculousSignDemand := true
  earlierPeopleSaidSame := true
  heartsAlike := true
  signsClear := true
  solidFaithReceivesSigns := true
  prophetSentWithTruth := true
  goodNewsBearing := true
  warningBearing := true
  notResponsibleForBlazePeople := true

structure GuidanceDesirePattern where
  jewsChristiansUnpleasedWithoutFollowing : Bool
  godsGuidanceOnlyTrueGuidance : Bool
  desiresAfterKnowledgeWarned : Bool
  noProtectorFromGod : Bool
  noHelperFromGod : Bool
  scriptureGiven : Bool
  scriptureFollowedAsDeserved : Bool
  trueBeliefInScripture : Bool
  deniersAreLosers : Bool
deriving DecidableEq, Repr

def guidanceDesirePattern : GuidanceDesirePattern where
  jewsChristiansUnpleasedWithoutFollowing := true
  godsGuidanceOnlyTrueGuidance := true
  desiresAfterKnowledgeWarned := true
  noProtectorFromGod := true
  noHelperFromGod := true
  scriptureGiven := true
  scriptureFollowedAsDeserved := true
  trueBeliefInScripture := true
  deniersAreLosers := true

theorem quran_al_baqara_transcendence_guidance_witness :
    transcendenceGuidanceMoments.length = 9
    ∧ transcendenceGuidanceMoments.head? =
        some TranscendenceGuidanceMoment.childClaimRejected
    ∧ transcendenceGuidanceMoments.getLast? =
        some TranscendenceGuidanceMoment.scriptureFollowedOrDenied
    ∧ transcendencePattern.childClaimRejected = true
    ∧ transcendencePattern.godExalted = true
    ∧ transcendencePattern.heavensEarthBelongToGod = true
    ∧ transcendencePattern.allDevoutlyObey = true
    ∧ transcendencePattern.originatorHeavensEarth = true
    ∧ transcendencePattern.beCommandEffective = true
    ∧ signsProphetPattern.unknowledgedSpeechDemand = true
    ∧ signsProphetPattern.miraculousSignDemand = true
    ∧ signsProphetPattern.heartsAlike = true
    ∧ signsProphetPattern.signsClear = true
    ∧ signsProphetPattern.prophetSentWithTruth = true
    ∧ signsProphetPattern.goodNewsBearing = true
    ∧ signsProphetPattern.warningBearing = true
    ∧ guidanceDesirePattern.godsGuidanceOnlyTrueGuidance = true
    ∧ guidanceDesirePattern.desiresAfterKnowledgeWarned = true
    ∧ guidanceDesirePattern.noProtectorFromGod = true
    ∧ guidanceDesirePattern.noHelperFromGod = true
    ∧ guidanceDesirePattern.scriptureFollowedAsDeserved = true
    ∧ guidanceDesirePattern.trueBeliefInScripture = true
    ∧ guidanceDesirePattern.deniersAreLosers = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end QuranAlBaqaraTranscendenceGuidanceWitness
end Gnosis.Witnesses.Islam
