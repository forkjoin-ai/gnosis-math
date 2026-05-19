import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Buddhist

/-!
# Dhammapada Twin Mind Witness

Witness ledger for `docs/ebooks/source-texts/dhammapada-muller.txt`,
chapter 1, "The Twin-Verses".

Mind roots speech and action; hatred cannot terminate hatred; truth requires
correct discrimination; recitation without practice is only external counting.
-/

structure ThoughtRootTrace where
  allFoundedOnThought : Bool := true
  evilThoughtPainFollows : Bool := true
  pureThoughtHappinessFollows : Bool := true
  traceFollowsLikeWheelOrShadow : Bool := true
deriving Repr, DecidableEq

structure HatredCessation where
  grievanceHarboringKeepsHatred : Bool := true
  grievanceReleaseCeasesHatred : Bool := true
  hatredNotCeasedByHatred : Bool := true
  hatredCeasedByLove : Bool := true
  endKnowledgeCeasesQuarrels : Bool := true
  uncontrolledPleasureWeakTree : Bool := true
  controlledSensesRockMountain : Bool := true
deriving Repr, DecidableEq

structure PracticeOverRecitation where
  uncleansedYellowDressUnworthy : Bool := true
  truthSeenAsTruthArrives : Bool := true
  passionBreaksUnreflectingMind : Bool := true
  reflectedMindKeepsPassionOut : Bool := true
  evilWorkRevealsSuffering : Bool := true
  pureWorkRevealsJoy : Bool := true
  recitationWithoutDoingCountsOthersCows : Bool := true
  smallLawPracticeSharesPriesthood : Bool := true
deriving Repr, DecidableEq

def thoughtRootTrace : ThoughtRootTrace := {}
def hatredCessation : HatredCessation := {}
def practiceOverRecitation : PracticeOverRecitation := {}

theorem dhammapada_thought_root_trace :
    thoughtRootTrace.allFoundedOnThought = true ∧
      thoughtRootTrace.evilThoughtPainFollows = true ∧
      thoughtRootTrace.pureThoughtHappinessFollows = true ∧
      thoughtRootTrace.traceFollowsLikeWheelOrShadow = true := by
  simp [thoughtRootTrace]

theorem dhammapada_hatred_cessation :
    hatredCessation.grievanceHarboringKeepsHatred = true ∧
      hatredCessation.grievanceReleaseCeasesHatred = true ∧
      hatredCessation.hatredNotCeasedByHatred = true ∧
      hatredCessation.hatredCeasedByLove = true ∧
      hatredCessation.endKnowledgeCeasesQuarrels = true ∧
      hatredCessation.uncontrolledPleasureWeakTree = true ∧
      hatredCessation.controlledSensesRockMountain = true := by
  simp [hatredCessation]

theorem dhammapada_practice_over_recitation :
    practiceOverRecitation.uncleansedYellowDressUnworthy = true ∧
      practiceOverRecitation.truthSeenAsTruthArrives = true ∧
      practiceOverRecitation.passionBreaksUnreflectingMind = true ∧
      practiceOverRecitation.reflectedMindKeepsPassionOut = true ∧
      practiceOverRecitation.evilWorkRevealsSuffering = true ∧
      practiceOverRecitation.pureWorkRevealsJoy = true ∧
      practiceOverRecitation.recitationWithoutDoingCountsOthersCows = true ∧
      practiceOverRecitation.smallLawPracticeSharesPriesthood = true := by
  simp [practiceOverRecitation]

theorem dhammapada_twin_mind_witness :
    thoughtRootTrace.allFoundedOnThought = true ∧
      hatredCessation.hatredNotCeasedByHatred = true ∧
      hatredCessation.hatredCeasedByLove = true ∧
      practiceOverRecitation.truthSeenAsTruthArrives = true ∧
      practiceOverRecitation.recitationWithoutDoingCountsOthersCows = true ∧
      practiceOverRecitation.smallLawPracticeSharesPriesthood = true := by
  simp [thoughtRootTrace, hatredCessation, practiceOverRecitation]

end Gnosis.Witnesses.Buddhist
