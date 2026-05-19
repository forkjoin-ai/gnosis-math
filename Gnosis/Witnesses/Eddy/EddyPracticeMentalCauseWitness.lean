import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyPracticeMentalCauseWitness

/-!
# Science and Health, Chapter XII -- Mental Cause in Practice

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:15340-15680`.

Bounded section: 370:1-378:18. Eddy gives the practice mechanics: the body
improves as thought spiritualizes, drug efficacy is treated as belief, diagnosis
induces fear, mortal mind governs bodily conditions, and Christian Science
adds mental and moral power rather than yielding the patient to mental
despotism.
-/

inductive PracticeMentalCauseMoment where
  | forsakeMortalSense
  | fearGoverningBodyBlocksHealth
  | faithInDrugSoleFactor
  | oppositeBeliefRemovesDrugEffect
  | healthFactsAffectBody
  | physicalDiagnosisInducesDisease
  | drugsHygieneQuackeryLosePotency
  | basisChangesToSpirit
  | bodySubstratumOfMortalMind
  | diseaseTalkLikeGhostStories
  | darknessFearNeedsScienceWayOut
  | mindImpartsHealth
  | brainNotMind
  | embodiedThoughtBindsItself
  | matterFalseSupportsFail
  | acknowledgeBenefits
  | diseaseMoreDocileThanSin
  | loveCastsOutFear
  | scientificHealthRelievesOrgan
  | mortalMindCirculatesBlood
  | truthOfBeingRelievesInflammation
  | hatredRemovedByLove
  | diseaseOriginatesInBelief
  | ignoranceOfCauseNoObjection
  | heatColdProductsOfMortalMind
  | changeMentalStateEndsFever
  | hypnotismMentalDespotism
  | scientistAddsMoralPower
  | palsyBeliefDestroyed
  | latentFearInConsumption
  | bloodNeverGaveLife
  | falseBeliefDestroyedByArgument
  | fearAdmissionParalyzesDemonstration
  | climateFearExterminated
  | mindStatesCauseStrengthWeakness
  | leadingFearRemovedDiseaseRemoved
  | diseaseNoIntelligence
  | truthControlsDisease
  | fearlessTruthFacesBelief
deriving DecidableEq, Repr

def practiceMentalCauseTrace : List PracticeMentalCauseMoment :=
  [ PracticeMentalCauseMoment.forsakeMortalSense
  , PracticeMentalCauseMoment.fearGoverningBodyBlocksHealth
  , PracticeMentalCauseMoment.faithInDrugSoleFactor
  , PracticeMentalCauseMoment.oppositeBeliefRemovesDrugEffect
  , PracticeMentalCauseMoment.healthFactsAffectBody
  , PracticeMentalCauseMoment.physicalDiagnosisInducesDisease
  , PracticeMentalCauseMoment.drugsHygieneQuackeryLosePotency
  , PracticeMentalCauseMoment.basisChangesToSpirit
  , PracticeMentalCauseMoment.bodySubstratumOfMortalMind
  , PracticeMentalCauseMoment.diseaseTalkLikeGhostStories
  , PracticeMentalCauseMoment.darknessFearNeedsScienceWayOut
  , PracticeMentalCauseMoment.mindImpartsHealth
  , PracticeMentalCauseMoment.brainNotMind
  , PracticeMentalCauseMoment.embodiedThoughtBindsItself
  , PracticeMentalCauseMoment.matterFalseSupportsFail
  , PracticeMentalCauseMoment.acknowledgeBenefits
  , PracticeMentalCauseMoment.diseaseMoreDocileThanSin
  , PracticeMentalCauseMoment.loveCastsOutFear
  , PracticeMentalCauseMoment.scientificHealthRelievesOrgan
  , PracticeMentalCauseMoment.mortalMindCirculatesBlood
  , PracticeMentalCauseMoment.truthOfBeingRelievesInflammation
  , PracticeMentalCauseMoment.hatredRemovedByLove
  , PracticeMentalCauseMoment.diseaseOriginatesInBelief
  , PracticeMentalCauseMoment.ignoranceOfCauseNoObjection
  , PracticeMentalCauseMoment.heatColdProductsOfMortalMind
  , PracticeMentalCauseMoment.changeMentalStateEndsFever
  , PracticeMentalCauseMoment.hypnotismMentalDespotism
  , PracticeMentalCauseMoment.scientistAddsMoralPower
  , PracticeMentalCauseMoment.palsyBeliefDestroyed
  , PracticeMentalCauseMoment.latentFearInConsumption
  , PracticeMentalCauseMoment.bloodNeverGaveLife
  , PracticeMentalCauseMoment.falseBeliefDestroyedByArgument
  , PracticeMentalCauseMoment.fearAdmissionParalyzesDemonstration
  , PracticeMentalCauseMoment.climateFearExterminated
  , PracticeMentalCauseMoment.mindStatesCauseStrengthWeakness
  , PracticeMentalCauseMoment.leadingFearRemovedDiseaseRemoved
  , PracticeMentalCauseMoment.diseaseNoIntelligence
  , PracticeMentalCauseMoment.truthControlsDisease
  , PracticeMentalCauseMoment.fearlessTruthFacesBelief
  ]

structure PracticeMentalCause where
  drugBeliefMechanism : Bool
  diagnosisFearRisk : Bool
  bodyMortalMindSubstratum : Bool
  diseaseCauseMental : Bool
  hypnotismRejected : Bool
  scientistIncreasesMoralPower : Bool
  fearRemovedDiseaseRemoved : Bool
  truthControlsDisease : Bool
deriving DecidableEq, Repr

def practiceMentalCause : PracticeMentalCause where
  drugBeliefMechanism := true
  diagnosisFearRisk := true
  bodyMortalMindSubstratum := true
  diseaseCauseMental := true
  hypnotismRejected := true
  scientistIncreasesMoralPower := true
  fearRemovedDiseaseRemoved := true
  truthControlsDisease := true

theorem eddy_practice_mental_cause_witness :
    practiceMentalCauseTrace.length = 39
    ∧ practiceMentalCauseTrace.head? =
      some PracticeMentalCauseMoment.forsakeMortalSense
    ∧ practiceMentalCauseTrace.getLast? =
      some PracticeMentalCauseMoment.fearlessTruthFacesBelief
    ∧ practiceMentalCause.drugBeliefMechanism = true
    ∧ practiceMentalCause.diagnosisFearRisk = true
    ∧ practiceMentalCause.bodyMortalMindSubstratum = true
    ∧ practiceMentalCause.diseaseCauseMental = true
    ∧ practiceMentalCause.hypnotismRejected = true
    ∧ practiceMentalCause.scientistIncreasesMoralPower = true
    ∧ practiceMentalCause.fearRemovedDiseaseRemoved = true
    ∧ practiceMentalCause.truthControlsDisease = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyPracticeMentalCauseWitness
end Gnosis.Witnesses.Eddy
