import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyPracticeContradictDiseaseWitness

/-!
# Science and Health, Chapter XII -- Contradicting Disease Testimony

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:16020-16380`.

Bounded section: 386:27-395:24. This practice unit treats grief, overwork,
food-theory, bodily symptoms, hereditary and climate fears, medical hopelessness,
and nursing practice as occasions for the same operation: refuse false testimony,
hold thought under Mind's government, and argue for Life rather than for disease.
-/

inductive ContradictDiseaseMoment where
  | mourningDeclaredCauseless
  | immortalMindNotOverworked
  | goodLaborNotPunished
  | martyrsWitnessProtectingMind
  | foodTheorySelfDivided
  | godSustainsLife
  | dietPenaltyCoupledWithBelief
  | pseudoMentalTestimonyDestroyed
  | ancientConfusionFalls
  | indigestionCaseReversed
  | harmonyRestoredByUnderstanding
  | firstSymptomsDisputed
  | symptomsOpposedLikeInhumanLaw
  | rebellionAgainstDiseaseSubmission
  | bodyComplaintNotPlea
  | fearFountainRebuked
  | physicalAffirmationMetByNegation
  | thoughtPorterGuardsDoor
  | mindMastersCorporealSense
  | matterCannotAche
  | sicknessUnrealUnderTruth
  | discordAdmissionDisarms
  | materialHopelessnessRejected
  | sickArgueAgainstSuffering
  | healerSpeaksWithAuthority
  | prayerAndNurseDiscipline
  | mentalQuackeryNamesRealDisease
deriving DecidableEq, Repr

def contradictDiseaseTrace : List ContradictDiseaseMoment :=
  [ ContradictDiseaseMoment.mourningDeclaredCauseless
  , ContradictDiseaseMoment.immortalMindNotOverworked
  , ContradictDiseaseMoment.goodLaborNotPunished
  , ContradictDiseaseMoment.martyrsWitnessProtectingMind
  , ContradictDiseaseMoment.foodTheorySelfDivided
  , ContradictDiseaseMoment.godSustainsLife
  , ContradictDiseaseMoment.dietPenaltyCoupledWithBelief
  , ContradictDiseaseMoment.pseudoMentalTestimonyDestroyed
  , ContradictDiseaseMoment.ancientConfusionFalls
  , ContradictDiseaseMoment.indigestionCaseReversed
  , ContradictDiseaseMoment.harmonyRestoredByUnderstanding
  , ContradictDiseaseMoment.firstSymptomsDisputed
  , ContradictDiseaseMoment.symptomsOpposedLikeInhumanLaw
  , ContradictDiseaseMoment.rebellionAgainstDiseaseSubmission
  , ContradictDiseaseMoment.bodyComplaintNotPlea
  , ContradictDiseaseMoment.fearFountainRebuked
  , ContradictDiseaseMoment.physicalAffirmationMetByNegation
  , ContradictDiseaseMoment.thoughtPorterGuardsDoor
  , ContradictDiseaseMoment.mindMastersCorporealSense
  , ContradictDiseaseMoment.matterCannotAche
  , ContradictDiseaseMoment.sicknessUnrealUnderTruth
  , ContradictDiseaseMoment.discordAdmissionDisarms
  , ContradictDiseaseMoment.materialHopelessnessRejected
  , ContradictDiseaseMoment.sickArgueAgainstSuffering
  , ContradictDiseaseMoment.healerSpeaksWithAuthority
  , ContradictDiseaseMoment.prayerAndNurseDiscipline
  , ContradictDiseaseMoment.mentalQuackeryNamesRealDisease
  ]

structure PracticeContradictDisease where
  griefDeniedAsCause : Bool
  overworkPenaltyDenied : Bool
  foodTheorySelfContradicts : Bool
  symptomsMustBeDisputed : Bool
  bodyCannotTestify : Bool
  fearMustBeCastOut : Bool
  thoughtGuardedAtDoor : Bool
  matterCannotFeelPain : Bool
  healerUsesAuthority : Bool
  diseaseRealityFastensError : Bool
deriving DecidableEq, Repr

def practiceContradictDisease : PracticeContradictDisease where
  griefDeniedAsCause := true
  overworkPenaltyDenied := true
  foodTheorySelfContradicts := true
  symptomsMustBeDisputed := true
  bodyCannotTestify := true
  fearMustBeCastOut := true
  thoughtGuardedAtDoor := true
  matterCannotFeelPain := true
  healerUsesAuthority := true
  diseaseRealityFastensError := true

theorem eddy_practice_contradict_disease_witness :
    contradictDiseaseTrace.length = 27
    ∧ contradictDiseaseTrace.head? =
      some ContradictDiseaseMoment.mourningDeclaredCauseless
    ∧ contradictDiseaseTrace.getLast? =
      some ContradictDiseaseMoment.mentalQuackeryNamesRealDisease
    ∧ practiceContradictDisease.griefDeniedAsCause = true
    ∧ practiceContradictDisease.overworkPenaltyDenied = true
    ∧ practiceContradictDisease.foodTheorySelfContradicts = true
    ∧ practiceContradictDisease.symptomsMustBeDisputed = true
    ∧ practiceContradictDisease.bodyCannotTestify = true
    ∧ practiceContradictDisease.fearMustBeCastOut = true
    ∧ practiceContradictDisease.thoughtGuardedAtDoor = true
    ∧ practiceContradictDisease.matterCannotFeelPain = true
    ∧ practiceContradictDisease.healerUsesAuthority = true
    ∧ practiceContradictDisease.diseaseRealityFastensError = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyPracticeContradictDiseaseWitness
end Gnosis.Witnesses.Eddy
