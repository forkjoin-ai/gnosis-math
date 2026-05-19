import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyScriptureStandpointPracticeWitness

/-!
# Science and Health, Chapter X -- Scripture, Standpoint, and Practice

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:13280-13580`.

Bounded section: 319:3-326:15. The unit turns from Christological proof to
method: Scripture needs spiritual interpretation, Moses' signs reduce serpent
and leprosy to mortal belief, standpoint must move from matter to Spirit, and
unused understanding decays unless practiced.
-/

inductive ScriptureStandpointMoment where
  | diseaseErrorVersusMind
  | lifeProspectsNotMateriallyCalculated
  | spiritMatterNeverConcur
  | godOnlyMindEndsMythologies
  | scriptureNeedsInspiration
  | misplacedWordMisstatesScience
  | namesExpressSpiritualIdeas
  | jobReadSpirituallyNotFleshly
  | mosesSerpentFearOvercome
  | leprosyMortalMindCreation
  | jesusDemonstratesMindSupremacy
  | standpointChangedToSpiritualBasis
  | finiteBeliefMustRelinquishError
  | sinPleasureMustYieldHigherSense
  | sufferingTurnsToDivineLove
  | strivingForsakesError
  | chastisementsHelpOnward
  | practiceWhatAlreadyKnown
  | unusedTalentDecays
  | needMakesReceptive
  | trueIdeaDestroysOtherMindsDelusion
  | childlikeReceptivity
  | purificationProofOfProgress
  | narrowWayConquersFlesh
  | paulBlindThenSpirituallyEnlightened
  | risenTruthNeededForBenefit
  | trueLifeLosesDeathBelief
  | beingIndestructibleInLife
  | consecrationRequired
  | falseSenseHidesDemonstration
  | noOtherRoadToScience
  | materialSystemsFullyForsaken
deriving DecidableEq, Repr

def scriptureStandpointTrace : List ScriptureStandpointMoment :=
  [ ScriptureStandpointMoment.diseaseErrorVersusMind
  , ScriptureStandpointMoment.lifeProspectsNotMateriallyCalculated
  , ScriptureStandpointMoment.spiritMatterNeverConcur
  , ScriptureStandpointMoment.godOnlyMindEndsMythologies
  , ScriptureStandpointMoment.scriptureNeedsInspiration
  , ScriptureStandpointMoment.misplacedWordMisstatesScience
  , ScriptureStandpointMoment.namesExpressSpiritualIdeas
  , ScriptureStandpointMoment.jobReadSpirituallyNotFleshly
  , ScriptureStandpointMoment.mosesSerpentFearOvercome
  , ScriptureStandpointMoment.leprosyMortalMindCreation
  , ScriptureStandpointMoment.jesusDemonstratesMindSupremacy
  , ScriptureStandpointMoment.standpointChangedToSpiritualBasis
  , ScriptureStandpointMoment.finiteBeliefMustRelinquishError
  , ScriptureStandpointMoment.sinPleasureMustYieldHigherSense
  , ScriptureStandpointMoment.sufferingTurnsToDivineLove
  , ScriptureStandpointMoment.strivingForsakesError
  , ScriptureStandpointMoment.chastisementsHelpOnward
  , ScriptureStandpointMoment.practiceWhatAlreadyKnown
  , ScriptureStandpointMoment.unusedTalentDecays
  , ScriptureStandpointMoment.needMakesReceptive
  , ScriptureStandpointMoment.trueIdeaDestroysOtherMindsDelusion
  , ScriptureStandpointMoment.childlikeReceptivity
  , ScriptureStandpointMoment.purificationProofOfProgress
  , ScriptureStandpointMoment.narrowWayConquersFlesh
  , ScriptureStandpointMoment.paulBlindThenSpirituallyEnlightened
  , ScriptureStandpointMoment.risenTruthNeededForBenefit
  , ScriptureStandpointMoment.trueLifeLosesDeathBelief
  , ScriptureStandpointMoment.beingIndestructibleInLife
  , ScriptureStandpointMoment.consecrationRequired
  , ScriptureStandpointMoment.falseSenseHidesDemonstration
  , ScriptureStandpointMoment.noOtherRoadToScience
  , ScriptureStandpointMoment.materialSystemsFullyForsaken
  ]

structure ScriptureStandpointPractice where
  scriptureRequiresSpiritualInterpretation : Bool
  serpentHandledByUnderstanding : Bool
  diseaseAsMortalMindCreation : Bool
  standpointMustChange : Bool
  sufferingWeansFromMatter : Bool
  practicePrecedesMoreApprehension : Bool
  childlikeReceptivityRequired : Bool
  paulPatternEnlightened : Bool
  lifeIdeaDestroysDeathBelief : Bool
  materialSystemsForsaken : Bool
deriving DecidableEq, Repr

def scriptureStandpointPractice : ScriptureStandpointPractice where
  scriptureRequiresSpiritualInterpretation := true
  serpentHandledByUnderstanding := true
  diseaseAsMortalMindCreation := true
  standpointMustChange := true
  sufferingWeansFromMatter := true
  practicePrecedesMoreApprehension := true
  childlikeReceptivityRequired := true
  paulPatternEnlightened := true
  lifeIdeaDestroysDeathBelief := true
  materialSystemsForsaken := true

theorem eddy_scripture_standpoint_practice_witness :
    scriptureStandpointTrace.length = 32
    ∧ scriptureStandpointTrace.head? =
      some ScriptureStandpointMoment.diseaseErrorVersusMind
    ∧ scriptureStandpointTrace.getLast? =
      some ScriptureStandpointMoment.materialSystemsFullyForsaken
    ∧ scriptureStandpointPractice.scriptureRequiresSpiritualInterpretation = true
    ∧ scriptureStandpointPractice.serpentHandledByUnderstanding = true
    ∧ scriptureStandpointPractice.diseaseAsMortalMindCreation = true
    ∧ scriptureStandpointPractice.standpointMustChange = true
    ∧ scriptureStandpointPractice.sufferingWeansFromMatter = true
    ∧ scriptureStandpointPractice.practicePrecedesMoreApprehension = true
    ∧ scriptureStandpointPractice.childlikeReceptivityRequired = true
    ∧ scriptureStandpointPractice.paulPatternEnlightened = true
    ∧ scriptureStandpointPractice.lifeIdeaDestroysDeathBelief = true
    ∧ scriptureStandpointPractice.materialSystemsForsaken = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyScriptureStandpointPracticeWitness
end Gnosis.Witnesses.Eddy
