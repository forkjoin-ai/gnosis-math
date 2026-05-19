import Init

namespace Gnosis.Witnesses.Bible.SecondCorinthians
namespace SecondCorinthiansExamineFinalGraceWitness

/-! # 2 Corinthians 13 -- Examine Yourselves and Final Grace
Source text: `docs/ebooks/source-texts/bible-kjv.txt:93527-93567`. -/

structure ExamineFinalGrace where
  twoOrThreeWitnessesEstablished : Bool
  proofChristSpeakingMightyInYou : Bool
  crucifiedWeakLivesPowerGod : Bool
  examineYourselvesInFaith : Bool
  doNoEvilDoHonest : Bool
  nothingAgainstTruthForTruth : Bool
  wishYourPerfection : Bool
  authorityEdificationNotDestruction : Bool
  farewellPerfectComfortOneMindPeace : Bool
  graceLoveCommunionBenediction : Bool
deriving DecidableEq, Repr

def examineFinalGrace : ExamineFinalGrace where
  twoOrThreeWitnessesEstablished := true
  proofChristSpeakingMightyInYou := true
  crucifiedWeakLivesPowerGod := true
  examineYourselvesInFaith := true
  doNoEvilDoHonest := true
  nothingAgainstTruthForTruth := true
  wishYourPerfection := true
  authorityEdificationNotDestruction := true
  farewellPerfectComfortOneMindPeace := true
  graceLoveCommunionBenediction := true

theorem second_corinthians_examine_final_grace_witness :
    examineFinalGrace.twoOrThreeWitnessesEstablished = true
    ∧ examineFinalGrace.proofChristSpeakingMightyInYou = true
    ∧ examineFinalGrace.crucifiedWeakLivesPowerGod = true
    ∧ examineFinalGrace.examineYourselvesInFaith = true
    ∧ examineFinalGrace.doNoEvilDoHonest = true
    ∧ examineFinalGrace.nothingAgainstTruthForTruth = true
    ∧ examineFinalGrace.wishYourPerfection = true
    ∧ examineFinalGrace.authorityEdificationNotDestruction = true
    ∧ examineFinalGrace.farewellPerfectComfortOneMindPeace = true
    ∧ examineFinalGrace.graceLoveCommunionBenediction = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SecondCorinthiansExamineFinalGraceWitness
end Gnosis.Witnesses.Bible.SecondCorinthians
