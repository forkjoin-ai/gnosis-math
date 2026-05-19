import Gnosis.GnosisTriptychBraid

namespace Gnosis.Witnesses.Buddhist

/-!
# Dhammapada Downward Classifier Witness

Witness ledger for `docs/ebooks/source-texts/dhammapada-muller.txt`,
chapter 22, "The Downward Course".
-/

structure FalseSpeechRobeGap where
  falseSpeechFallsDownward : Bool := true
  denialAfterDoingFallsDownward : Bool := true
  yellowGownUnrestrainedFallsDownward : Bool := true
  charityMisusedByBadUnrestrained : Bool := true
  badlyPracticedAsceticismCutsLikeGrassBlade : Bool := true
deriving Repr, DecidableEq

structure CarelessPractice where
  carelessActNoReward : Bool := true
  brokenVowNoReward : Bool := true
  hesitatingDisciplineNoReward : Bool := true
  vigorousDoingRequired : Bool := true
  carelessPilgrimScattersPassionDust : Bool := true
  goodDeedBetterDone : Bool := true
  selfGuardedLikeFrontierFort : Bool := true
  momentNotAllowedToEscape : Bool := true
deriving Repr, DecidableEq

structure InvertedPredicatePath where
  shameInvertedEvilPath : Bool := true
  fearInvertedEvilPath : Bool := true
  forbiddenInvertedEvilPath : Bool := true
  forbiddenKnownAsForbiddenGoodPath : Bool := true
  notForbiddenKnownAsNotForbiddenGoodPath : Bool := true
  trueDoctrineGoodPath : Bool := true
deriving Repr, DecidableEq

def falseSpeechRobeGap : FalseSpeechRobeGap := {}
def carelessPractice : CarelessPractice := {}
def invertedPredicatePath : InvertedPredicatePath := {}

theorem dhammapada_false_speech_robe_gap :
    falseSpeechRobeGap.falseSpeechFallsDownward = true ∧
      falseSpeechRobeGap.denialAfterDoingFallsDownward = true ∧
      falseSpeechRobeGap.yellowGownUnrestrainedFallsDownward = true ∧
      falseSpeechRobeGap.charityMisusedByBadUnrestrained = true ∧
      falseSpeechRobeGap.badlyPracticedAsceticismCutsLikeGrassBlade = true := by
  simp [falseSpeechRobeGap]

theorem dhammapada_careless_practice :
    carelessPractice.carelessActNoReward = true ∧
      carelessPractice.brokenVowNoReward = true ∧
      carelessPractice.hesitatingDisciplineNoReward = true ∧
      carelessPractice.vigorousDoingRequired = true ∧
      carelessPractice.carelessPilgrimScattersPassionDust = true ∧
      carelessPractice.goodDeedBetterDone = true ∧
      carelessPractice.selfGuardedLikeFrontierFort = true ∧
      carelessPractice.momentNotAllowedToEscape = true := by
  simp [carelessPractice]

theorem dhammapada_inverted_predicate_path :
    invertedPredicatePath.shameInvertedEvilPath = true ∧
      invertedPredicatePath.fearInvertedEvilPath = true ∧
      invertedPredicatePath.forbiddenInvertedEvilPath = true ∧
      invertedPredicatePath.forbiddenKnownAsForbiddenGoodPath = true ∧
      invertedPredicatePath.notForbiddenKnownAsNotForbiddenGoodPath = true ∧
      invertedPredicatePath.trueDoctrineGoodPath = true := by
  simp [invertedPredicatePath]

theorem dhammapada_downward_classifier_witness :
    falseSpeechRobeGap.falseSpeechFallsDownward = true ∧
      falseSpeechRobeGap.yellowGownUnrestrainedFallsDownward = true ∧
      carelessPractice.carelessPilgrimScattersPassionDust = true ∧
      carelessPractice.selfGuardedLikeFrontierFort = true ∧
      invertedPredicatePath.shameInvertedEvilPath = true ∧
      invertedPredicatePath.forbiddenKnownAsForbiddenGoodPath = true ∧
      invertedPredicatePath.trueDoctrineGoodPath = true := by
  simp [falseSpeechRobeGap, carelessPractice, invertedPredicatePath]

end Gnosis.Witnesses.Buddhist
