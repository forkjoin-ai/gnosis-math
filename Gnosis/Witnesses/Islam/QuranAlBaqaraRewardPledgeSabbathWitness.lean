import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraRewardPledgeSabbathWitness

/-!
# Quran 2:62-66, Al-Baqara -- Reward, Pledge, Sabbath Lesson

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1131-1142`.

This bounded witness tracks the short bridge before the cow narrative:

  * believers, Jews, Christians, and Sabians are named together;
  * belief in God and the Last Day with good action receives reward;
  * no fear and no grief are promised;
  * the pledge is taken with the mountain raised above them;
  * holding fast and bearing contents in mind serve consciousness of God;
  * turning away is answered by divine favor and mercy;
  * Sabbath-breaking becomes an example and a lesson for the mindful.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive RewardPledgeSabbathMoment
  | inclusiveReward
  | noFearNoGrief
  | mountainPledge
  | holdFastRemember
  | mercyAfterTurning
  | sabbathTransgression
  | exampleAndLesson
deriving DecidableEq, Repr

def rewardPledgeSabbathMoments : List RewardPledgeSabbathMoment :=
  [ RewardPledgeSabbathMoment.inclusiveReward
  , RewardPledgeSabbathMoment.noFearNoGrief
  , RewardPledgeSabbathMoment.mountainPledge
  , RewardPledgeSabbathMoment.holdFastRemember
  , RewardPledgeSabbathMoment.mercyAfterTurning
  , RewardPledgeSabbathMoment.sabbathTransgression
  , RewardPledgeSabbathMoment.exampleAndLesson
  ]

structure RewardPattern where
  muslimBelieversNamed : Bool
  jewsNamed : Bool
  christiansNamed : Bool
  sabiansNamed : Bool
  believeGod : Bool
  believeLastDay : Bool
  doGood : Bool
  rewardWithLord : Bool
  noFear : Bool
  noGrief : Bool
deriving DecidableEq, Repr

def rewardPattern : RewardPattern where
  muslimBelieversNamed := true
  jewsNamed := true
  christiansNamed := true
  sabiansNamed := true
  believeGod := true
  believeLastDay := true
  doGood := true
  rewardWithLord := true
  noFear := true
  noGrief := true

structure PledgeMercyPattern where
  pledgeTaken : Bool
  mountainRaisedAbove : Bool
  holdFastCommanded : Bool
  contentsBorneInMind : Bool
  consciousnessOfGodAim : Bool
  turningAwayNamed : Bool
  divineFavorNamed : Bool
  divineMercyNamed : Bool
  lossAverted : Bool
deriving DecidableEq, Repr

def pledgeMercyPattern : PledgeMercyPattern where
  pledgeTaken := true
  mountainRaisedAbove := true
  holdFastCommanded := true
  contentsBorneInMind := true
  consciousnessOfGodAim := true
  turningAwayNamed := true
  divineFavorNamed := true
  divineMercyNamed := true
  lossAverted := true

structure SabbathLessonPattern where
  sabbathBreakersKnown : Bool
  outcastJudgmentSpoken : Bool
  exampleForContemporaries : Bool
  exampleForLaterPeople : Bool
  lessonForMindful : Bool
deriving DecidableEq, Repr

def sabbathLessonPattern : SabbathLessonPattern where
  sabbathBreakersKnown := true
  outcastJudgmentSpoken := true
  exampleForContemporaries := true
  exampleForLaterPeople := true
  lessonForMindful := true

theorem quran_al_baqara_reward_pledge_sabbath_witness :
    rewardPledgeSabbathMoments.length = 7
    ∧ rewardPledgeSabbathMoments.head? = some RewardPledgeSabbathMoment.inclusiveReward
    ∧ rewardPledgeSabbathMoments.getLast? = some RewardPledgeSabbathMoment.exampleAndLesson
    ∧ rewardPattern.muslimBelieversNamed = true
    ∧ rewardPattern.jewsNamed = true
    ∧ rewardPattern.christiansNamed = true
    ∧ rewardPattern.sabiansNamed = true
    ∧ rewardPattern.believeGod = true
    ∧ rewardPattern.believeLastDay = true
    ∧ rewardPattern.doGood = true
    ∧ rewardPattern.rewardWithLord = true
    ∧ rewardPattern.noFear = true
    ∧ rewardPattern.noGrief = true
    ∧ pledgeMercyPattern.pledgeTaken = true
    ∧ pledgeMercyPattern.mountainRaisedAbove = true
    ∧ pledgeMercyPattern.holdFastCommanded = true
    ∧ pledgeMercyPattern.consciousnessOfGodAim = true
    ∧ pledgeMercyPattern.turningAwayNamed = true
    ∧ pledgeMercyPattern.divineFavorNamed = true
    ∧ pledgeMercyPattern.divineMercyNamed = true
    ∧ pledgeMercyPattern.lossAverted = true
    ∧ sabbathLessonPattern.sabbathBreakersKnown = true
    ∧ sabbathLessonPattern.outcastJudgmentSpoken = true
    ∧ sabbathLessonPattern.exampleForLaterPeople = true
    ∧ sabbathLessonPattern.lessonForMindful = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · rfl
  · rfl

end QuranAlBaqaraRewardPledgeSabbathWitness
end Gnosis.Witnesses.Islam
