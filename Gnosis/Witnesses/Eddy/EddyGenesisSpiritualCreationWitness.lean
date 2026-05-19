import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyGenesisSpiritualCreationWitness

/-!
# Science and Health, Chapter XV -- Spiritual Creation

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:20455-21640`.

Bounded section: 501:1-521:18. This Genesis unit interprets the first creation
record as spiritual actuality: one creator and creation, light before sun,
firmament as understanding, plant and seed as Mind's ideas, ascending spiritual
days, man as reflected likeness, dominion as birthright, and rest as holy action.
-/

inductive GenesisSpiritualCreationMoment where
  | interpretationBeginsGenesis
  | genesisUntrueImageContrastsActualMan
  | beginningMeansOnlyEternalUnity
  | oneCreatorOneCreation
  | ideasUnfoldInMind
  | harmonyWhereMatterUnknown
  | lightAsGodIdea
  | lightSeparatedFromDarkness
  | truthRevelationBeforeSun
  | eveningsMorningsClearerViews
  | matterDarknessSupposedSpiritAbsence
  | firmamentSpiritualUnderstanding
  | understandingDemarcatesRealUnreal
  | matterNoRealEntity
  | exaltedThoughtSecondDay
  | thoughtsGatheredIntoChannels
  | dryLandAbsoluteFormations
  | spiritNamesAndBlesses
  | divinePropagationByMind
  | creationEverAppearing
  | genderMentalKind
  | thirdDayResurrectionSense
  | celestialLightsRarefyThought
  | divineNatureAppearing
  | spiritualIdeasApprehended
  | sunSymbolSoulOutsideBody
  | geologyCannotExplainFormation
  | lightSymbolMind
  | darknessScatteredNoNight
  | aspirationsAboveCorporeality
  | seraphicSymbolsHolyThoughts
  | pureIdeasMultiply
  | spiritualSpheresAppear
  | thoughtsDiversifiedBySpirit
  | godThoughtsSpiritualRealities
  | moralCourageLion
  | harmlessUsefulCreatures
  | serpentHarmlessAsWiseIdea
  | elohimPluralityTriunity
  | manFamilyNameForIdeas
  | mirrorReflectionScience
  | loveImpartsBeauty
  | manWomanCoexistentWithGod
  | genericManNotAnthropomorphicGod
  | divinePersonalityReflected
  | dominionBirthright
  | brotherhoodProtectsLesserIdea
  | perfectionOfCreation
  | infinityMeasureless
  | godRestsInAction
  | loveAndManCoexistent
  | growthFromMind
  | spiritualNarrativeComplete
deriving DecidableEq, Repr

def genesisSpiritualCreationTrace : List GenesisSpiritualCreationMoment :=
  [ GenesisSpiritualCreationMoment.interpretationBeginsGenesis
  , GenesisSpiritualCreationMoment.genesisUntrueImageContrastsActualMan
  , GenesisSpiritualCreationMoment.beginningMeansOnlyEternalUnity
  , GenesisSpiritualCreationMoment.oneCreatorOneCreation
  , GenesisSpiritualCreationMoment.ideasUnfoldInMind
  , GenesisSpiritualCreationMoment.harmonyWhereMatterUnknown
  , GenesisSpiritualCreationMoment.lightAsGodIdea
  , GenesisSpiritualCreationMoment.lightSeparatedFromDarkness
  , GenesisSpiritualCreationMoment.truthRevelationBeforeSun
  , GenesisSpiritualCreationMoment.eveningsMorningsClearerViews
  , GenesisSpiritualCreationMoment.matterDarknessSupposedSpiritAbsence
  , GenesisSpiritualCreationMoment.firmamentSpiritualUnderstanding
  , GenesisSpiritualCreationMoment.understandingDemarcatesRealUnreal
  , GenesisSpiritualCreationMoment.matterNoRealEntity
  , GenesisSpiritualCreationMoment.exaltedThoughtSecondDay
  , GenesisSpiritualCreationMoment.thoughtsGatheredIntoChannels
  , GenesisSpiritualCreationMoment.dryLandAbsoluteFormations
  , GenesisSpiritualCreationMoment.spiritNamesAndBlesses
  , GenesisSpiritualCreationMoment.divinePropagationByMind
  , GenesisSpiritualCreationMoment.creationEverAppearing
  , GenesisSpiritualCreationMoment.genderMentalKind
  , GenesisSpiritualCreationMoment.thirdDayResurrectionSense
  , GenesisSpiritualCreationMoment.celestialLightsRarefyThought
  , GenesisSpiritualCreationMoment.divineNatureAppearing
  , GenesisSpiritualCreationMoment.spiritualIdeasApprehended
  , GenesisSpiritualCreationMoment.sunSymbolSoulOutsideBody
  , GenesisSpiritualCreationMoment.geologyCannotExplainFormation
  , GenesisSpiritualCreationMoment.lightSymbolMind
  , GenesisSpiritualCreationMoment.darknessScatteredNoNight
  , GenesisSpiritualCreationMoment.aspirationsAboveCorporeality
  , GenesisSpiritualCreationMoment.seraphicSymbolsHolyThoughts
  , GenesisSpiritualCreationMoment.pureIdeasMultiply
  , GenesisSpiritualCreationMoment.spiritualSpheresAppear
  , GenesisSpiritualCreationMoment.thoughtsDiversifiedBySpirit
  , GenesisSpiritualCreationMoment.godThoughtsSpiritualRealities
  , GenesisSpiritualCreationMoment.moralCourageLion
  , GenesisSpiritualCreationMoment.harmlessUsefulCreatures
  , GenesisSpiritualCreationMoment.serpentHarmlessAsWiseIdea
  , GenesisSpiritualCreationMoment.elohimPluralityTriunity
  , GenesisSpiritualCreationMoment.manFamilyNameForIdeas
  , GenesisSpiritualCreationMoment.mirrorReflectionScience
  , GenesisSpiritualCreationMoment.loveImpartsBeauty
  , GenesisSpiritualCreationMoment.manWomanCoexistentWithGod
  , GenesisSpiritualCreationMoment.genericManNotAnthropomorphicGod
  , GenesisSpiritualCreationMoment.divinePersonalityReflected
  , GenesisSpiritualCreationMoment.dominionBirthright
  , GenesisSpiritualCreationMoment.brotherhoodProtectsLesserIdea
  , GenesisSpiritualCreationMoment.perfectionOfCreation
  , GenesisSpiritualCreationMoment.infinityMeasureless
  , GenesisSpiritualCreationMoment.godRestsInAction
  , GenesisSpiritualCreationMoment.loveAndManCoexistent
  , GenesisSpiritualCreationMoment.growthFromMind
  , GenesisSpiritualCreationMoment.spiritualNarrativeComplete
  ]

structure GenesisSpiritualCreation where
  oneCreatorOneCreation : Bool
  lightIsTruthRevelation : Bool
  firmamentUnderstanding : Bool
  creationIdeasNotMatter : Bool
  manReflectsGod : Bool
  dominionBirthright : Bool
  creationCompleteGood : Bool
  restHolyAction : Bool
deriving DecidableEq, Repr

def genesisSpiritualCreation : GenesisSpiritualCreation where
  oneCreatorOneCreation := true
  lightIsTruthRevelation := true
  firmamentUnderstanding := true
  creationIdeasNotMatter := true
  manReflectsGod := true
  dominionBirthright := true
  creationCompleteGood := true
  restHolyAction := true

theorem eddy_genesis_spiritual_creation_witness :
    genesisSpiritualCreationTrace.length = 53
    ∧ genesisSpiritualCreationTrace.head? =
      some GenesisSpiritualCreationMoment.interpretationBeginsGenesis
    ∧ genesisSpiritualCreationTrace.getLast? =
      some GenesisSpiritualCreationMoment.spiritualNarrativeComplete
    ∧ genesisSpiritualCreation.oneCreatorOneCreation = true
    ∧ genesisSpiritualCreation.lightIsTruthRevelation = true
    ∧ genesisSpiritualCreation.firmamentUnderstanding = true
    ∧ genesisSpiritualCreation.creationIdeasNotMatter = true
    ∧ genesisSpiritualCreation.manReflectsGod = true
    ∧ genesisSpiritualCreation.dominionBirthright = true
    ∧ genesisSpiritualCreation.creationCompleteGood = true
    ∧ genesisSpiritualCreation.restHolyAction = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyGenesisSpiritualCreationWitness
end Gnosis.Witnesses.Eddy
