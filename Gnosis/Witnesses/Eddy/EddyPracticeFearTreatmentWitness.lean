import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyPracticeFearTreatmentWitness

/-!
# Science and Health, Chapter XII -- Fear and Mental Treatment

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:16880-17380`.

Bounded section: 407:27-414:30. This practice unit names sin and sickness as
forms of error, rejects drug/brain causation, denies death as a teacher, begins
mental treatment from "Be not afraid," and applies fear-removal to named
disease, infants, juvenile ailments, and insanity.
-/

inductive FearTreatmentMoment where
  | sinClassedAsInsanity
  | sicknessLossOfHarmony
  | universalHealthInsanity
  | drugsCannotReachMindThroughMatter
  | brainJointDifferenceBelief
  | sensationInMatterUnreal
  | intelligentMatterImpossible
  | unconsciousBodyCannotDictate
  | animateGovernedByGod
  | mortalPutOffForTrueModel
  | deathNoBenefactor
  | lifeEternalPresentKnowledge
  | truthActualLife
  | trialStrengthensFaith
  | perfectLoveCastsFear
  | mentalPracticeNoMisuse
  | beNotAfraidKeynote
  | silentNamingStudentAid
  | loveWitnessInstantaneous
  | legionSelfSeenDestroyed
  | fearIgnoranceSinFoundation
  | diseaseThoughtExternalized
  | beginByAllayingFear
  | silentPleadingFromGovernance
  | audibleNamingCanImpress
  | argumentBreaksSenseDream
  | harmonyInsistedUntilBodyCorresponds
  | infantMetThroughParentThought
  | heredityDeniedByMatterUnintelligence
  | parentalViewsAffectChildren
  | hygieneKeptSimple
  | symptomAttentionEducatesDiscord
  | insanityYieldsToTruth
  | matterBrainCannotDerangeMind
  | explanationTimedToReadiness
  | manPerfectModelHeld
deriving DecidableEq, Repr

def fearTreatmentTrace : List FearTreatmentMoment :=
  [ FearTreatmentMoment.sinClassedAsInsanity
  , FearTreatmentMoment.sicknessLossOfHarmony
  , FearTreatmentMoment.universalHealthInsanity
  , FearTreatmentMoment.drugsCannotReachMindThroughMatter
  , FearTreatmentMoment.brainJointDifferenceBelief
  , FearTreatmentMoment.sensationInMatterUnreal
  , FearTreatmentMoment.intelligentMatterImpossible
  , FearTreatmentMoment.unconsciousBodyCannotDictate
  , FearTreatmentMoment.animateGovernedByGod
  , FearTreatmentMoment.mortalPutOffForTrueModel
  , FearTreatmentMoment.deathNoBenefactor
  , FearTreatmentMoment.lifeEternalPresentKnowledge
  , FearTreatmentMoment.truthActualLife
  , FearTreatmentMoment.trialStrengthensFaith
  , FearTreatmentMoment.perfectLoveCastsFear
  , FearTreatmentMoment.mentalPracticeNoMisuse
  , FearTreatmentMoment.beNotAfraidKeynote
  , FearTreatmentMoment.silentNamingStudentAid
  , FearTreatmentMoment.loveWitnessInstantaneous
  , FearTreatmentMoment.legionSelfSeenDestroyed
  , FearTreatmentMoment.fearIgnoranceSinFoundation
  , FearTreatmentMoment.diseaseThoughtExternalized
  , FearTreatmentMoment.beginByAllayingFear
  , FearTreatmentMoment.silentPleadingFromGovernance
  , FearTreatmentMoment.audibleNamingCanImpress
  , FearTreatmentMoment.argumentBreaksSenseDream
  , FearTreatmentMoment.harmonyInsistedUntilBodyCorresponds
  , FearTreatmentMoment.infantMetThroughParentThought
  , FearTreatmentMoment.heredityDeniedByMatterUnintelligence
  , FearTreatmentMoment.parentalViewsAffectChildren
  , FearTreatmentMoment.hygieneKeptSimple
  , FearTreatmentMoment.symptomAttentionEducatesDiscord
  , FearTreatmentMoment.insanityYieldsToTruth
  , FearTreatmentMoment.matterBrainCannotDerangeMind
  , FearTreatmentMoment.explanationTimedToReadiness
  , FearTreatmentMoment.manPerfectModelHeld
  ]

structure PracticeFearTreatment where
  sinAndSicknessErrors : Bool
  drugsCannotTreatMindThroughMatter : Bool
  deathDoesNotTeachLife : Bool
  treatmentBeginsByAllayingFear : Bool
  diseaseThoughtExternalized : Bool
  namingDiseaseIsConditional : Bool
  hereditaryDiseaseDenied : Bool
  childrenEducatedByMentalImages : Bool
  insanityTreatedLikeOtherDisease : Bool
  perfectModelHeld : Bool
deriving DecidableEq, Repr

def practiceFearTreatment : PracticeFearTreatment where
  sinAndSicknessErrors := true
  drugsCannotTreatMindThroughMatter := true
  deathDoesNotTeachLife := true
  treatmentBeginsByAllayingFear := true
  diseaseThoughtExternalized := true
  namingDiseaseIsConditional := true
  hereditaryDiseaseDenied := true
  childrenEducatedByMentalImages := true
  insanityTreatedLikeOtherDisease := true
  perfectModelHeld := true

theorem eddy_practice_fear_treatment_witness :
    fearTreatmentTrace.length = 36
    ∧ fearTreatmentTrace.head? =
      some FearTreatmentMoment.sinClassedAsInsanity
    ∧ fearTreatmentTrace.getLast? =
      some FearTreatmentMoment.manPerfectModelHeld
    ∧ practiceFearTreatment.sinAndSicknessErrors = true
    ∧ practiceFearTreatment.drugsCannotTreatMindThroughMatter = true
    ∧ practiceFearTreatment.deathDoesNotTeachLife = true
    ∧ practiceFearTreatment.treatmentBeginsByAllayingFear = true
    ∧ practiceFearTreatment.diseaseThoughtExternalized = true
    ∧ practiceFearTreatment.namingDiseaseIsConditional = true
    ∧ practiceFearTreatment.hereditaryDiseaseDenied = true
    ∧ practiceFearTreatment.childrenEducatedByMentalImages = true
    ∧ practiceFearTreatment.insanityTreatedLikeOtherDisease = true
    ∧ practiceFearTreatment.perfectModelHeld = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyPracticeFearTreatmentWitness
end Gnosis.Witnesses.Eddy
