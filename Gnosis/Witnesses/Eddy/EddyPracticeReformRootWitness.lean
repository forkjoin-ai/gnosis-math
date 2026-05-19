import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyPracticeReformRootWitness

/-!
# Science and Health, Chapter XII -- Reform Root and Error Removal

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:16680-16880`.

Bounded section: 403:1-407:27. This practice unit gathers wrongdoing,
appetite, fear, hatred, repentance, sickness, resistance, craving, and memory
loss as reform problems rooted in mortal belief rather than matter. Healing and
reforming converge through moral correction, divine Mind's mastery, and the
replacement of the demoralized model by the perfect one.
-/

inductive ReformRootMoment where
  | selfMesmerismBeliefInducesDisease
  | voluntaryMesmerismMakesWrongdoerSuffer
  | bothOriginsHumanMind
  | mortalExistenceSelfDeception
  | errorImaginaryPowerSweptByTruth
  | rectitudeBestForHealing
  | patientNotBurdenedByForeboding
  | practitionerConclusionHelpsOrHarms
  | appetiteDestroyedByTruthOfBeing
  | falsePleasureDenied
  | corruptMindManifestedInBody
  | reformationCancelsCrimeEffect
  | temperanceReformMetaphysical
  | sinPleasureDeniedStrengthensCourage
  | sickHealingAndSinnerReformOneMethod
  | fearHatredDishonestyMakeSick
  | mortalMindBasicError
  | propensitiesMasteredByOpposites
  | moralLawSentenceBalancesAccount
  | sinDestroysItself
  | guiltyConscienceCumulative
  | sufferingTurnsFromBodyToSpirit
  | bibleTreeHealingRecipe
  | loveCastsOutFear
  | sicknessAbatesAsSenseSubdued
  | resistErrorToEnd
  | cravingsDestroyedByMindMastery
  | panaceaStrengthensMortalWeakness
  | wrongDesireYieldsToScience
  | memoryLossContradicted
  | perfectModelAdmitted
deriving DecidableEq, Repr

def reformRootTrace : List ReformRootMoment :=
  [ ReformRootMoment.selfMesmerismBeliefInducesDisease
  , ReformRootMoment.voluntaryMesmerismMakesWrongdoerSuffer
  , ReformRootMoment.bothOriginsHumanMind
  , ReformRootMoment.mortalExistenceSelfDeception
  , ReformRootMoment.errorImaginaryPowerSweptByTruth
  , ReformRootMoment.rectitudeBestForHealing
  , ReformRootMoment.patientNotBurdenedByForeboding
  , ReformRootMoment.practitionerConclusionHelpsOrHarms
  , ReformRootMoment.appetiteDestroyedByTruthOfBeing
  , ReformRootMoment.falsePleasureDenied
  , ReformRootMoment.corruptMindManifestedInBody
  , ReformRootMoment.reformationCancelsCrimeEffect
  , ReformRootMoment.temperanceReformMetaphysical
  , ReformRootMoment.sinPleasureDeniedStrengthensCourage
  , ReformRootMoment.sickHealingAndSinnerReformOneMethod
  , ReformRootMoment.fearHatredDishonestyMakeSick
  , ReformRootMoment.mortalMindBasicError
  , ReformRootMoment.propensitiesMasteredByOpposites
  , ReformRootMoment.moralLawSentenceBalancesAccount
  , ReformRootMoment.sinDestroysItself
  , ReformRootMoment.guiltyConscienceCumulative
  , ReformRootMoment.sufferingTurnsFromBodyToSpirit
  , ReformRootMoment.bibleTreeHealingRecipe
  , ReformRootMoment.loveCastsOutFear
  , ReformRootMoment.sicknessAbatesAsSenseSubdued
  , ReformRootMoment.resistErrorToEnd
  , ReformRootMoment.cravingsDestroyedByMindMastery
  , ReformRootMoment.panaceaStrengthensMortalWeakness
  , ReformRootMoment.wrongDesireYieldsToScience
  , ReformRootMoment.memoryLossContradicted
  , ReformRootMoment.perfectModelAdmitted
  ]

structure PracticeReformRoot where
  diseaseAndWrongdoingMentalOrigin : Bool
  practitionerConclusionMatters : Bool
  falsePleasureMustBeDenied : Bool
  healingAndReformSameMethod : Bool
  fearSinRootSickness : Bool
  oppositesMasterPropensities : Bool
  loveCastsOutFear : Bool
  cravingsYieldToMind : Bool
  perfectModelReplacesLoss : Bool
deriving DecidableEq, Repr

def practiceReformRoot : PracticeReformRoot where
  diseaseAndWrongdoingMentalOrigin := true
  practitionerConclusionMatters := true
  falsePleasureMustBeDenied := true
  healingAndReformSameMethod := true
  fearSinRootSickness := true
  oppositesMasterPropensities := true
  loveCastsOutFear := true
  cravingsYieldToMind := true
  perfectModelReplacesLoss := true

theorem eddy_practice_reform_root_witness :
    reformRootTrace.length = 31
    ∧ reformRootTrace.head? =
      some ReformRootMoment.selfMesmerismBeliefInducesDisease
    ∧ reformRootTrace.getLast? =
      some ReformRootMoment.perfectModelAdmitted
    ∧ practiceReformRoot.diseaseAndWrongdoingMentalOrigin = true
    ∧ practiceReformRoot.practitionerConclusionMatters = true
    ∧ practiceReformRoot.falsePleasureMustBeDenied = true
    ∧ practiceReformRoot.healingAndReformSameMethod = true
    ∧ practiceReformRoot.fearSinRootSickness = true
    ∧ practiceReformRoot.oppositesMasterPropensities = true
    ∧ practiceReformRoot.loveCastsOutFear = true
    ∧ practiceReformRoot.cravingsYieldToMind = true
    ∧ practiceReformRoot.perfectModelReplacesLoss = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyPracticeReformRootWitness
end Gnosis.Witnesses.Eddy
