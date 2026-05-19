import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraDevotionInheritanceWitness

/-!
# Quran 2:131-134, Al-Baqara -- Devotion, Jacob, Accountability

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1379-1390`.

This bounded witness tracks Abraham's devotion and Jacob's deathbed continuity:

  * Abraham is told to devote himself to God and replies with devotion to the Lord of the Universe;
  * Abraham commands his sons, and Jacob does the same;
  * the chosen religion is to be held through the dying moment;
  * Jacob asks what his sons will worship after him;
  * they answer with worship of one single God, the God of Abraham, Ishmael, and Isaac;
  * that community has passed away, with earned deeds belonging to each side.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive DevotionInheritanceMoment
  | abrahamDevotionCommand
  | lordUniverseReply
  | sonsCommanded
  | jacobCommanded
  | dyingMomentDevotion
  | jacobDeathbedQuestion
  | oneGodAnswer
  | communityPassedAway
  | separateEarnings
deriving DecidableEq, Repr

def devotionInheritanceMoments : List DevotionInheritanceMoment :=
  [ DevotionInheritanceMoment.abrahamDevotionCommand
  , DevotionInheritanceMoment.lordUniverseReply
  , DevotionInheritanceMoment.sonsCommanded
  , DevotionInheritanceMoment.jacobCommanded
  , DevotionInheritanceMoment.dyingMomentDevotion
  , DevotionInheritanceMoment.jacobDeathbedQuestion
  , DevotionInheritanceMoment.oneGodAnswer
  , DevotionInheritanceMoment.communityPassedAway
  , DevotionInheritanceMoment.separateEarnings
  ]

structure DevotionCommandPattern where
  lordCommandsDevotion : Bool
  abrahamRepliesDevotion : Bool
  lordUniverseNamed : Bool
  abrahamCommandsSons : Bool
  jacobCommandsSons : Bool
  religionChosenByGod : Bool
  devotionUntilDeath : Bool
deriving DecidableEq, Repr

def devotionCommandPattern : DevotionCommandPattern where
  lordCommandsDevotion := true
  abrahamRepliesDevotion := true
  lordUniverseNamed := true
  abrahamCommandsSons := true
  jacobCommandsSons := true
  religionChosenByGod := true
  devotionUntilDeath := true

structure JacobWitnessPattern where
  jacobDeathNamed : Bool
  worshipAfterQuestion : Bool
  worshipYourGodAnswer : Bool
  fathersGodNamed : Bool
  abrahamNamed : Bool
  ishmaelNamed : Bool
  isaacNamed : Bool
  oneSingleGod : Bool
  devotionToHim : Bool
deriving DecidableEq, Repr

def jacobWitnessPattern : JacobWitnessPattern where
  jacobDeathNamed := true
  worshipAfterQuestion := true
  worshipYourGodAnswer := true
  fathersGodNamed := true
  abrahamNamed := true
  ishmaelNamed := true
  isaacNamed := true
  oneSingleGod := true
  devotionToHim := true

structure CommunityAccountabilityPattern where
  communityPassedAway : Bool
  theirEarningsBelongToThem : Bool
  yourEarningsBelongToYou : Bool
  notAnswerableForTheirDeeds : Bool
deriving DecidableEq, Repr

def communityAccountabilityPattern : CommunityAccountabilityPattern where
  communityPassedAway := true
  theirEarningsBelongToThem := true
  yourEarningsBelongToYou := true
  notAnswerableForTheirDeeds := true

theorem quran_al_baqara_devotion_inheritance_witness :
    devotionInheritanceMoments.length = 9
    ∧ devotionInheritanceMoments.head? = some DevotionInheritanceMoment.abrahamDevotionCommand
    ∧ devotionInheritanceMoments.getLast? = some DevotionInheritanceMoment.separateEarnings
    ∧ devotionCommandPattern.lordCommandsDevotion = true
    ∧ devotionCommandPattern.abrahamRepliesDevotion = true
    ∧ devotionCommandPattern.lordUniverseNamed = true
    ∧ devotionCommandPattern.abrahamCommandsSons = true
    ∧ devotionCommandPattern.jacobCommandsSons = true
    ∧ devotionCommandPattern.religionChosenByGod = true
    ∧ devotionCommandPattern.devotionUntilDeath = true
    ∧ jacobWitnessPattern.jacobDeathNamed = true
    ∧ jacobWitnessPattern.worshipAfterQuestion = true
    ∧ jacobWitnessPattern.abrahamNamed = true
    ∧ jacobWitnessPattern.ishmaelNamed = true
    ∧ jacobWitnessPattern.isaacNamed = true
    ∧ jacobWitnessPattern.oneSingleGod = true
    ∧ jacobWitnessPattern.devotionToHim = true
    ∧ communityAccountabilityPattern.communityPassedAway = true
    ∧ communityAccountabilityPattern.theirEarningsBelongToThem = true
    ∧ communityAccountabilityPattern.yourEarningsBelongToYou = true
    ∧ communityAccountabilityPattern.notAnswerableForTheirDeeds = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

end QuranAlBaqaraDevotionInheritanceWitness
end Gnosis.Witnesses.Islam
