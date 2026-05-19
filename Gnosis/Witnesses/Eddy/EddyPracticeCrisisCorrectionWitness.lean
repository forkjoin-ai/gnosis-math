import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyPracticeCrisisCorrectionWitness

/-!
# Science and Health, Chapter XII -- Crisis Correction and Re-formation

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:17340-17620`.

Bounded section: 420:9-426:3. This practice unit tracks reassurance,
startling the patient awake, crisis/chemicalization, the book as physician,
bone-healing, scientific correction, accidents, hereditary disease, consumption,
and sound lungs as a sequence of belief-correction and bodily re-formation.
-/

inductive CrisisCorrectionMoment where
  | invalidsTaughtNotHelpless
  | truthStimulatesBetterThanDrug
  | loveGivesPowerOverCondition
  | patientAwakenedFromDream
  | derangementAsDisturbedHarmony
  | crisisTreatedAsMentalDisturbance
  | noDiseaseGroundInsisted
  | chemicalizationCalmed
  | diseaseNotSeenNorBuiltUp
  | falseMathPerversion
  | bookCanAllayTruthTremor
  | mentalMoralChemistryReconstructs
  | spiritAlchemyDestroysSinDeath
  | surgeonMatterFearInvitesDefeat
  | unexpressedFearAffectsPatient
  | scientificCorrectiveStartsWithMind
  | metaphysicianStrengthensPatient
  | bonesFormedAsThoughtPhenomena
  | accidentsUnknownToGod
  | divineMindRemovesObstacles
  | aloneWithGodAndSickPreferred
  | hereditaryBeliefDestroyed
  | mortalMindInducesHumorConclusion
  | consumptionPointsTreatedAsBeliefs
  | matterNeverSustainsExistence
  | consciousnessConstructsBetterBody
  | lungsMaintainedByMentalProtest
  | truthSteersBodyToHealth
deriving DecidableEq, Repr

def crisisCorrectionTrace : List CrisisCorrectionMoment :=
  [ CrisisCorrectionMoment.invalidsTaughtNotHelpless
  , CrisisCorrectionMoment.truthStimulatesBetterThanDrug
  , CrisisCorrectionMoment.loveGivesPowerOverCondition
  , CrisisCorrectionMoment.patientAwakenedFromDream
  , CrisisCorrectionMoment.derangementAsDisturbedHarmony
  , CrisisCorrectionMoment.crisisTreatedAsMentalDisturbance
  , CrisisCorrectionMoment.noDiseaseGroundInsisted
  , CrisisCorrectionMoment.chemicalizationCalmed
  , CrisisCorrectionMoment.diseaseNotSeenNorBuiltUp
  , CrisisCorrectionMoment.falseMathPerversion
  , CrisisCorrectionMoment.bookCanAllayTruthTremor
  , CrisisCorrectionMoment.mentalMoralChemistryReconstructs
  , CrisisCorrectionMoment.spiritAlchemyDestroysSinDeath
  , CrisisCorrectionMoment.surgeonMatterFearInvitesDefeat
  , CrisisCorrectionMoment.unexpressedFearAffectsPatient
  , CrisisCorrectionMoment.scientificCorrectiveStartsWithMind
  , CrisisCorrectionMoment.metaphysicianStrengthensPatient
  , CrisisCorrectionMoment.bonesFormedAsThoughtPhenomena
  , CrisisCorrectionMoment.accidentsUnknownToGod
  , CrisisCorrectionMoment.divineMindRemovesObstacles
  , CrisisCorrectionMoment.aloneWithGodAndSickPreferred
  , CrisisCorrectionMoment.hereditaryBeliefDestroyed
  , CrisisCorrectionMoment.mortalMindInducesHumorConclusion
  , CrisisCorrectionMoment.consumptionPointsTreatedAsBeliefs
  , CrisisCorrectionMoment.matterNeverSustainsExistence
  , CrisisCorrectionMoment.consciousnessConstructsBetterBody
  , CrisisCorrectionMoment.lungsMaintainedByMentalProtest
  , CrisisCorrectionMoment.truthSteersBodyToHealth
  ]

structure PracticeCrisisCorrection where
  patientNotHelpless : Bool
  crisisMentalDisturbance : Bool
  chemicalizationFavorableWhenExplained : Bool
  materialApplicationRejected : Bool
  fearAffectsOutcome : Bool
  correctionStartsWithMind : Bool
  accidentsUnknownToGod : Bool
  heredityBeliefDestroyed : Bool
  consciousnessReformsBody : Bool
deriving DecidableEq, Repr

def practiceCrisisCorrection : PracticeCrisisCorrection where
  patientNotHelpless := true
  crisisMentalDisturbance := true
  chemicalizationFavorableWhenExplained := true
  materialApplicationRejected := true
  fearAffectsOutcome := true
  correctionStartsWithMind := true
  accidentsUnknownToGod := true
  heredityBeliefDestroyed := true
  consciousnessReformsBody := true

theorem eddy_practice_crisis_correction_witness :
    crisisCorrectionTrace.length = 28
    ∧ crisisCorrectionTrace.head? =
      some CrisisCorrectionMoment.invalidsTaughtNotHelpless
    ∧ crisisCorrectionTrace.getLast? =
      some CrisisCorrectionMoment.truthSteersBodyToHealth
    ∧ practiceCrisisCorrection.patientNotHelpless = true
    ∧ practiceCrisisCorrection.crisisMentalDisturbance = true
    ∧ practiceCrisisCorrection.chemicalizationFavorableWhenExplained = true
    ∧ practiceCrisisCorrection.materialApplicationRejected = true
    ∧ practiceCrisisCorrection.fearAffectsOutcome = true
    ∧ practiceCrisisCorrection.correctionStartsWithMind = true
    ∧ practiceCrisisCorrection.accidentsUnknownToGod = true
    ∧ practiceCrisisCorrection.heredityBeliefDestroyed = true
    ∧ practiceCrisisCorrection.consciousnessReformsBody = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyPracticeCrisisCorrectionWitness
end Gnosis.Witnesses.Eddy
