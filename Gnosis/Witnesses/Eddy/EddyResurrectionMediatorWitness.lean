import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyResurrectionMediatorWitness

/-!
# Science and Health, Chapter X -- Resurrection, Mediator, and Sickness

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:13080-13280`.

Bounded section: 314:1-319:1. Eddy reads resurrection as proof of one Mind,
not material substance; Jesus mediates by demonstrating Spirit over flesh;
Thomas records the material-sense demand for proof; sickness is treated as
discord, not as man's identity.
-/

inductive ResurrectionMediatorMoment where
  | jesusProvesFatherReflectionInseparable
  | oneMindWithoutSecond
  | mindBuilderOfTemple
  | materialismMissesTrueJesus
  | maryReceivesLifeSubstanceIdea
  | resurrectionDisprovesMaterialLawOfDeath
  | oneMindSeparatesFromRabbinicTheology
  | egoMindNotBody
  | sonshipHiddenByCarnalMind
  | sinSubduedRevealsHeritage
  | spiritualOriginDemonstratesBeing
  | jesusMediatorSpiritFlesh
  | mortalsTurnFromSinFindChrist
  | truthEffectsHealBodyMind
  | christIdeaCannotBeKilledByFlesh
  | christPresentsIndestructibleMan
  | materialKnowledgeUsurpsPrinciple
  | followersDrinkMastersCup
  | spiritualIndividualityMoreTangible
  | thomasNeedsMaterialDisplay
  | corporealSensesOriginateMaterialError
  | materialSenseLieMustBeSilenced
  | sicknessDiscordNotImage
  | truthHealsSensationError
  | materialMedicineTreatsDiseaseAsReal
  | governorNotSubjectToGoverned
  | bodyDoesNotIncludeSoul
deriving DecidableEq, Repr

def resurrectionMediatorTrace : List ResurrectionMediatorMoment :=
  [ ResurrectionMediatorMoment.jesusProvesFatherReflectionInseparable
  , ResurrectionMediatorMoment.oneMindWithoutSecond
  , ResurrectionMediatorMoment.mindBuilderOfTemple
  , ResurrectionMediatorMoment.materialismMissesTrueJesus
  , ResurrectionMediatorMoment.maryReceivesLifeSubstanceIdea
  , ResurrectionMediatorMoment.resurrectionDisprovesMaterialLawOfDeath
  , ResurrectionMediatorMoment.oneMindSeparatesFromRabbinicTheology
  , ResurrectionMediatorMoment.egoMindNotBody
  , ResurrectionMediatorMoment.sonshipHiddenByCarnalMind
  , ResurrectionMediatorMoment.sinSubduedRevealsHeritage
  , ResurrectionMediatorMoment.spiritualOriginDemonstratesBeing
  , ResurrectionMediatorMoment.jesusMediatorSpiritFlesh
  , ResurrectionMediatorMoment.mortalsTurnFromSinFindChrist
  , ResurrectionMediatorMoment.truthEffectsHealBodyMind
  , ResurrectionMediatorMoment.christIdeaCannotBeKilledByFlesh
  , ResurrectionMediatorMoment.christPresentsIndestructibleMan
  , ResurrectionMediatorMoment.materialKnowledgeUsurpsPrinciple
  , ResurrectionMediatorMoment.followersDrinkMastersCup
  , ResurrectionMediatorMoment.spiritualIndividualityMoreTangible
  , ResurrectionMediatorMoment.thomasNeedsMaterialDisplay
  , ResurrectionMediatorMoment.corporealSensesOriginateMaterialError
  , ResurrectionMediatorMoment.materialSenseLieMustBeSilenced
  , ResurrectionMediatorMoment.sicknessDiscordNotImage
  , ResurrectionMediatorMoment.truthHealsSensationError
  , ResurrectionMediatorMoment.materialMedicineTreatsDiseaseAsReal
  , ResurrectionMediatorMoment.governorNotSubjectToGoverned
  , ResurrectionMediatorMoment.bodyDoesNotIncludeSoul
  ]

structure ResurrectionMediator where
  oneMindWithoutSecond : Bool
  resurrectionDisprovesDeathLaw : Bool
  jesusMediatorByDemonstration : Bool
  christIdeaIndestructible : Bool
  thomasMaterialSenseDemand : Bool
  sicknessDiscordNotIdentity : Bool
  truthHealsSensationError : Bool
  governorNotGoverned : Bool
deriving DecidableEq, Repr

def resurrectionMediator : ResurrectionMediator where
  oneMindWithoutSecond := true
  resurrectionDisprovesDeathLaw := true
  jesusMediatorByDemonstration := true
  christIdeaIndestructible := true
  thomasMaterialSenseDemand := true
  sicknessDiscordNotIdentity := true
  truthHealsSensationError := true
  governorNotGoverned := true

theorem eddy_resurrection_mediator_witness :
    resurrectionMediatorTrace.length = 27
    ∧ resurrectionMediatorTrace.head? =
      some ResurrectionMediatorMoment.jesusProvesFatherReflectionInseparable
    ∧ resurrectionMediatorTrace.getLast? =
      some ResurrectionMediatorMoment.bodyDoesNotIncludeSoul
    ∧ resurrectionMediator.oneMindWithoutSecond = true
    ∧ resurrectionMediator.resurrectionDisprovesDeathLaw = true
    ∧ resurrectionMediator.jesusMediatorByDemonstration = true
    ∧ resurrectionMediator.christIdeaIndestructible = true
    ∧ resurrectionMediator.thomasMaterialSenseDemand = true
    ∧ resurrectionMediator.sicknessDiscordNotIdentity = true
    ∧ resurrectionMediator.truthHealsSensationError = true
    ∧ resurrectionMediator.governorNotGoverned = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyResurrectionMediatorWitness
end Gnosis.Witnesses.Eddy
