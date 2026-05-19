import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraPilgrimageConductWitness

/-!
# Quran 2:197-202, Al-Baqara -- Pilgrimage Conduct and Prayer Horizon

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1669-1698`.

This bounded witness tracks pilgrimage conduct and prayer horizon:

  * pilgrimage happens in prescribed months;
  * indecent speech, misbehaviour, and quarrelling are barred;
  * God knows whatever good is done;
  * provision is commanded, and the best provision is mindfulness;
  * seeking bounty from the Lord is no offence;
  * Arafat descent, sacred-place remembrance, guidance from prior straying, and forgiveness are named;
  * completed rites intensify remembrance beyond remembrance of fathers;
  * worldly-only prayer has no Hereafter share, while world-and-Hereafter prayer seeks Fire protection;
  * earned share and swift reckoning close the unit.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive PilgrimageConductMoment
  | prescribedMonths
  | conductBounds
  | goodKnown
  | mindfulProvision
  | bountyPermitted
  | arafatRemembrance
  | forgivenessAsked
  | completedRitesRemembrance
  | prayerHorizons
  | earnedShareReckoning
deriving DecidableEq, Repr

def pilgrimageConductMoments : List PilgrimageConductMoment :=
  [ PilgrimageConductMoment.prescribedMonths
  , PilgrimageConductMoment.conductBounds
  , PilgrimageConductMoment.goodKnown
  , PilgrimageConductMoment.mindfulProvision
  , PilgrimageConductMoment.bountyPermitted
  , PilgrimageConductMoment.arafatRemembrance
  , PilgrimageConductMoment.forgivenessAsked
  , PilgrimageConductMoment.completedRitesRemembrance
  , PilgrimageConductMoment.prayerHorizons
  , PilgrimageConductMoment.earnedShareReckoning
  ]

structure PilgrimageConductPattern where
  prescribedMonths : Bool
  noIndecentSpeech : Bool
  noMisbehaviour : Bool
  noQuarrelling : Bool
  godAwareOfGood : Bool
  provideForYourselves : Bool
  bestProvisionMindfulness : Bool
  mindfulAddressToUnderstanding : Bool
deriving DecidableEq, Repr

def pilgrimageConductPattern : PilgrimageConductPattern where
  prescribedMonths := true
  noIndecentSpeech := true
  noMisbehaviour := true
  noQuarrelling := true
  godAwareOfGood := true
  provideForYourselves := true
  bestProvisionMindfulness := true
  mindfulAddressToUnderstanding := true

structure RemembrancePrayerPattern where
  bountySeekingNoOffence : Bool
  arafatSurgeDown : Bool
  sacredPlaceRememberGod : Bool
  guidanceAfterStraying : Bool
  surgeWithPeople : Bool
  askForgiveness : Bool
  godForgivingMerciful : Bool
  ritesCompleted : Bool
  rememberMoreThanFathers : Bool
  worldlyOnlyPrayer : Bool
  noHereafterShare : Bool
  worldAndHereafterGoodPrayer : Bool
  fireProtectionPrayer : Bool
  earnedShare : Bool
  swiftReckoning : Bool
deriving DecidableEq, Repr

def remembrancePrayerPattern : RemembrancePrayerPattern where
  bountySeekingNoOffence := true
  arafatSurgeDown := true
  sacredPlaceRememberGod := true
  guidanceAfterStraying := true
  surgeWithPeople := true
  askForgiveness := true
  godForgivingMerciful := true
  ritesCompleted := true
  rememberMoreThanFathers := true
  worldlyOnlyPrayer := true
  noHereafterShare := true
  worldAndHereafterGoodPrayer := true
  fireProtectionPrayer := true
  earnedShare := true
  swiftReckoning := true

theorem quran_al_baqara_pilgrimage_conduct_witness :
    pilgrimageConductMoments.length = 10
    ∧ pilgrimageConductMoments.head? = some PilgrimageConductMoment.prescribedMonths
    ∧ pilgrimageConductMoments.getLast? = some PilgrimageConductMoment.earnedShareReckoning
    ∧ pilgrimageConductPattern.prescribedMonths = true
    ∧ pilgrimageConductPattern.noIndecentSpeech = true
    ∧ pilgrimageConductPattern.noMisbehaviour = true
    ∧ pilgrimageConductPattern.noQuarrelling = true
    ∧ pilgrimageConductPattern.godAwareOfGood = true
    ∧ pilgrimageConductPattern.bestProvisionMindfulness = true
    ∧ remembrancePrayerPattern.bountySeekingNoOffence = true
    ∧ remembrancePrayerPattern.arafatSurgeDown = true
    ∧ remembrancePrayerPattern.sacredPlaceRememberGod = true
    ∧ remembrancePrayerPattern.guidanceAfterStraying = true
    ∧ remembrancePrayerPattern.askForgiveness = true
    ∧ remembrancePrayerPattern.godForgivingMerciful = true
    ∧ remembrancePrayerPattern.ritesCompleted = true
    ∧ remembrancePrayerPattern.rememberMoreThanFathers = true
    ∧ remembrancePrayerPattern.worldlyOnlyPrayer = true
    ∧ remembrancePrayerPattern.noHereafterShare = true
    ∧ remembrancePrayerPattern.worldAndHereafterGoodPrayer = true
    ∧ remembrancePrayerPattern.fireProtectionPrayer = true
    ∧ remembrancePrayerPattern.earnedShare = true
    ∧ remembrancePrayerPattern.swiftReckoning = true := by
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

end QuranAlBaqaraPilgrimageConductWitness
end Gnosis.Witnesses.Islam
