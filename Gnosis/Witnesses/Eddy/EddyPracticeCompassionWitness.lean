import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyPracticeCompassionWitness

/-!
# Science and Health, Chapter XII -- Practice and Compassion

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:15023-15340`.

Bounded section: 362:1-370:1. Christian Science Practice opens with the
Magdalene/Simon contrast: healing practice requires repentance, compassion,
spiritual affection, and moral self-purgation. The counterproof is the
unloving practitioner, who cannot give what spiritual barrenness withholds.
-/

inductive PracticeCompassionMoment where
  | magdaleneBreaksSocialBoundary
  | jesusReadsHiddenJudgment
  | debtParableMeasuresLove
  | griefEvidenceOfRepentance
  | penitenceOutweighsHospitality
  | simonSeeksPersonalHomage
  | genuineRepentanceLovesMuch
  | compassionRequisiteForSick
  | divineLoveReachesPatient
  | hypocrisyDesecratesHealingRoom
  | patientNeedsPeacePatienceLove
  | healerCastsOutOwnMoralEvils
  | sympathyRequiredForPhysician
  | calmBeforeSinAndDisease
  | bindBrokenHeartedFirst
  | tenderWordBetterThanTheories
  | gratitudeHumilityMagdalenePattern
  | saltAndLightPractice
  | truthInfiniteErrorNothing
  | moreFaithInTruthEnablesHealing
  | lifeIndependentOfMatter
  | matterAdmissionSupportsDisease
  | matterLossMakesManMaster
  | christTreatmentDoesNotRealityDisease
  | noTwoLives
  | noHealingInWillfulError
deriving DecidableEq, Repr

def practiceCompassionTrace : List PracticeCompassionMoment :=
  [ PracticeCompassionMoment.magdaleneBreaksSocialBoundary
  , PracticeCompassionMoment.jesusReadsHiddenJudgment
  , PracticeCompassionMoment.debtParableMeasuresLove
  , PracticeCompassionMoment.griefEvidenceOfRepentance
  , PracticeCompassionMoment.penitenceOutweighsHospitality
  , PracticeCompassionMoment.simonSeeksPersonalHomage
  , PracticeCompassionMoment.genuineRepentanceLovesMuch
  , PracticeCompassionMoment.compassionRequisiteForSick
  , PracticeCompassionMoment.divineLoveReachesPatient
  , PracticeCompassionMoment.hypocrisyDesecratesHealingRoom
  , PracticeCompassionMoment.patientNeedsPeacePatienceLove
  , PracticeCompassionMoment.healerCastsOutOwnMoralEvils
  , PracticeCompassionMoment.sympathyRequiredForPhysician
  , PracticeCompassionMoment.calmBeforeSinAndDisease
  , PracticeCompassionMoment.bindBrokenHeartedFirst
  , PracticeCompassionMoment.tenderWordBetterThanTheories
  , PracticeCompassionMoment.gratitudeHumilityMagdalenePattern
  , PracticeCompassionMoment.saltAndLightPractice
  , PracticeCompassionMoment.truthInfiniteErrorNothing
  , PracticeCompassionMoment.moreFaithInTruthEnablesHealing
  , PracticeCompassionMoment.lifeIndependentOfMatter
  , PracticeCompassionMoment.matterAdmissionSupportsDisease
  , PracticeCompassionMoment.matterLossMakesManMaster
  , PracticeCompassionMoment.christTreatmentDoesNotRealityDisease
  , PracticeCompassionMoment.noTwoLives
  , PracticeCompassionMoment.noHealingInWillfulError
  ]

structure PracticeCompassion where
  repentanceOutweighsStatus : Bool
  compassionRequired : Bool
  healerMustSelfPurge : Bool
  tenderPracticeOverTheory : Bool
  errorNothingBeforeTruth : Bool
  lifeIndependentOfMatter : Bool
  diseaseNotMadeReality : Bool
  noHealingInWillfulError : Bool
deriving DecidableEq, Repr

def practiceCompassion : PracticeCompassion where
  repentanceOutweighsStatus := true
  compassionRequired := true
  healerMustSelfPurge := true
  tenderPracticeOverTheory := true
  errorNothingBeforeTruth := true
  lifeIndependentOfMatter := true
  diseaseNotMadeReality := true
  noHealingInWillfulError := true

theorem eddy_practice_compassion_witness :
    practiceCompassionTrace.length = 26
    ∧ practiceCompassionTrace.head? =
      some PracticeCompassionMoment.magdaleneBreaksSocialBoundary
    ∧ practiceCompassionTrace.getLast? =
      some PracticeCompassionMoment.noHealingInWillfulError
    ∧ practiceCompassion.repentanceOutweighsStatus = true
    ∧ practiceCompassion.compassionRequired = true
    ∧ practiceCompassion.healerMustSelfPurge = true
    ∧ practiceCompassion.tenderPracticeOverTheory = true
    ∧ practiceCompassion.errorNothingBeforeTruth = true
    ∧ practiceCompassion.lifeIndependentOfMatter = true
    ∧ practiceCompassion.diseaseNotMadeReality = true
    ∧ practiceCompassion.noHealingInWillfulError = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyPracticeCompassionWitness
end Gnosis.Witnesses.Eddy
