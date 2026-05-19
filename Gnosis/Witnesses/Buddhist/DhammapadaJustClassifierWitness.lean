import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Buddhist

/-!
# Dhammapada Just Classifier Witness

Witness ledger for `docs/ebooks/source-texts/dhammapada-muller.txt`,
chapter 19, "The Just".
-/

structure BehavioralJustice where
  violenceDoesNotMakeJust : Bool := true
  rightWrongDistinguished : Bool := true
  leadsByLawEquity : Bool := true
  guardedByLawIntelligent : Bool := true
  muchTalkDoesNotMakeLearned : Bool := true
  patienceHatredFearFreeLearned : Bool := true
deriving Repr, DecidableEq

structure LabelCounterproofs where
  littleLearnedLawSeenBodily : Bool := true
  greyHairNotElder : Bool := true
  truthVirtueLoveRestraintElder : Bool := true
  beautyTalkNotRespectable : Bool := true
  tonsureDoesNotMakeSamana : Bool := true
  beggingDoesNotMakeBhikshu : Bool := true
  silenceDoesNotMakeMuni : Bool := true
  nonInjuryMakesAriya : Bool := true
deriving Repr, DecidableEq

structure DesireExtinctionGuard where
  evilQuietedMakesSamana : Bool := true
  wholeLawAdoptedMakesBhikshu : Bool := true
  balanceChoosesGoodAvoidsEvil : Bool := true
  pityForAllLivingCreatures : Bool := true
  disciplineVowsLearningTranceInsufficient : Bool := true
  confidenceUnsafeBeforeDesireExtinction : Bool := true
deriving Repr, DecidableEq

def behavioralJustice : BehavioralJustice := {}
def labelCounterproofs : LabelCounterproofs := {}
def desireExtinctionGuard : DesireExtinctionGuard := {}

theorem dhammapada_behavioral_justice :
    behavioralJustice.violenceDoesNotMakeJust = true ∧
      behavioralJustice.rightWrongDistinguished = true ∧
      behavioralJustice.leadsByLawEquity = true ∧
      behavioralJustice.guardedByLawIntelligent = true ∧
      behavioralJustice.muchTalkDoesNotMakeLearned = true ∧
      behavioralJustice.patienceHatredFearFreeLearned = true := by
  simp [behavioralJustice]

theorem dhammapada_label_counterproofs :
    labelCounterproofs.littleLearnedLawSeenBodily = true ∧
      labelCounterproofs.greyHairNotElder = true ∧
      labelCounterproofs.truthVirtueLoveRestraintElder = true ∧
      labelCounterproofs.beautyTalkNotRespectable = true ∧
      labelCounterproofs.tonsureDoesNotMakeSamana = true ∧
      labelCounterproofs.beggingDoesNotMakeBhikshu = true ∧
      labelCounterproofs.silenceDoesNotMakeMuni = true ∧
      labelCounterproofs.nonInjuryMakesAriya = true := by
  simp [labelCounterproofs]

theorem dhammapada_desire_extinction_guard :
    desireExtinctionGuard.evilQuietedMakesSamana = true ∧
      desireExtinctionGuard.wholeLawAdoptedMakesBhikshu = true ∧
      desireExtinctionGuard.balanceChoosesGoodAvoidsEvil = true ∧
      desireExtinctionGuard.pityForAllLivingCreatures = true ∧
      desireExtinctionGuard.disciplineVowsLearningTranceInsufficient = true ∧
      desireExtinctionGuard.confidenceUnsafeBeforeDesireExtinction = true := by
  simp [desireExtinctionGuard]

theorem dhammapada_just_classifier_witness :
    behavioralJustice.violenceDoesNotMakeJust = true ∧
      behavioralJustice.leadsByLawEquity = true ∧
      labelCounterproofs.greyHairNotElder = true ∧
      labelCounterproofs.tonsureDoesNotMakeSamana = true ∧
      labelCounterproofs.nonInjuryMakesAriya = true ∧
      desireExtinctionGuard.disciplineVowsLearningTranceInsufficient = true ∧
      desireExtinctionGuard.confidenceUnsafeBeforeDesireExtinction = true := by
  simp [behavioralJustice, labelCounterproofs, desireExtinctionGuard]

end Gnosis.Witnesses.Buddhist
