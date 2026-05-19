import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyGenesisEvolutionCounterWitness

/-!
# Science and Health, Chapter XV -- Evolution Counter-Witness

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:22460-22697`.

Bounded section: 547:9-557:27. This Genesis closing unit uses Agassiz, Darwin,
embryology, species, eggs, and physiology as counter-witnesses against material
origin, then returns to Mind as the real producer, ontology over physiology, and
the curse removed as man is seen as never born and never dying.
-/

inductive GenesisEvolutionCounterMoment where
  | agassizOvumStrengthensQuestion
  | darwinMaterialEvolutionConsistentError
  | firstCauseCannotBecomeMatter
  | scriptureUnderstoodSpiritually
  | trueUniverseSpiritualDevelopment
  | perceptionLiftsFromDiseaseDeath
  | manNeverLostEstate
  | corporealCloudsRollAway
  | mortalAgonyHelpsDestroyError
  | naturalistPredictionChange
  | selfDivisionCorroboratesMindScience
  | eggLifeMistake
  | threeReproductionProcessesHypotheses
  | materialResearchPhysicsWithoutMetaphysics
  | agassizDropsToMaterialOrigin
  | lifeMindNotInEgg
  | godPreservesIndividuality
  | spiritNotDevelopedThroughOpposite
  | materialStagesHideLife
  | eggImpossibleEnclosureDeity
  | speciesDoNotProduceOpposites
  | mindProducesOrProduced
  | likeProducesLike
  | evolutionGradationsHumanBelief
  | matterCannotTransmitMind
  | allMindOrAllMatter
  | causationNotInMatter
  | mortalTheoriesFriendFatalTriad
  | mortalsPeckShellsUpward
  | matterSurrendersClaims
  | betterBasisThanEmbryology
  | nativityInThought
  | noMortalityBeingImmortal
  | errorImputesMortalityToGod
  | devilAsMindInMatterFalsity
  | animalsShowLessMortalMindLessDisease
  | errorNoEntityPower
  | originManLikeOriginGod
  | creationSpiritualBasis
  | jesusRestoresVanishedManifestation
  | generaMaterialConcepts
  | formerThingsPassAway
  | christianPrivilegeFathomsScience
  | adamSleepAsDream
  | ontologyBeforePhysiology
  | birthThroesBelief
  | curseRemovedByMistEvaporation
  | manNeverBornNeverDying
  | firstGenesisStandardRestored
deriving DecidableEq, Repr

def genesisEvolutionCounterTrace : List GenesisEvolutionCounterMoment :=
  [ GenesisEvolutionCounterMoment.agassizOvumStrengthensQuestion
  , GenesisEvolutionCounterMoment.darwinMaterialEvolutionConsistentError
  , GenesisEvolutionCounterMoment.firstCauseCannotBecomeMatter
  , GenesisEvolutionCounterMoment.scriptureUnderstoodSpiritually
  , GenesisEvolutionCounterMoment.trueUniverseSpiritualDevelopment
  , GenesisEvolutionCounterMoment.perceptionLiftsFromDiseaseDeath
  , GenesisEvolutionCounterMoment.manNeverLostEstate
  , GenesisEvolutionCounterMoment.corporealCloudsRollAway
  , GenesisEvolutionCounterMoment.mortalAgonyHelpsDestroyError
  , GenesisEvolutionCounterMoment.naturalistPredictionChange
  , GenesisEvolutionCounterMoment.selfDivisionCorroboratesMindScience
  , GenesisEvolutionCounterMoment.eggLifeMistake
  , GenesisEvolutionCounterMoment.threeReproductionProcessesHypotheses
  , GenesisEvolutionCounterMoment.materialResearchPhysicsWithoutMetaphysics
  , GenesisEvolutionCounterMoment.agassizDropsToMaterialOrigin
  , GenesisEvolutionCounterMoment.lifeMindNotInEgg
  , GenesisEvolutionCounterMoment.godPreservesIndividuality
  , GenesisEvolutionCounterMoment.spiritNotDevelopedThroughOpposite
  , GenesisEvolutionCounterMoment.materialStagesHideLife
  , GenesisEvolutionCounterMoment.eggImpossibleEnclosureDeity
  , GenesisEvolutionCounterMoment.speciesDoNotProduceOpposites
  , GenesisEvolutionCounterMoment.mindProducesOrProduced
  , GenesisEvolutionCounterMoment.likeProducesLike
  , GenesisEvolutionCounterMoment.evolutionGradationsHumanBelief
  , GenesisEvolutionCounterMoment.matterCannotTransmitMind
  , GenesisEvolutionCounterMoment.allMindOrAllMatter
  , GenesisEvolutionCounterMoment.causationNotInMatter
  , GenesisEvolutionCounterMoment.mortalTheoriesFriendFatalTriad
  , GenesisEvolutionCounterMoment.mortalsPeckShellsUpward
  , GenesisEvolutionCounterMoment.matterSurrendersClaims
  , GenesisEvolutionCounterMoment.betterBasisThanEmbryology
  , GenesisEvolutionCounterMoment.nativityInThought
  , GenesisEvolutionCounterMoment.noMortalityBeingImmortal
  , GenesisEvolutionCounterMoment.errorImputesMortalityToGod
  , GenesisEvolutionCounterMoment.devilAsMindInMatterFalsity
  , GenesisEvolutionCounterMoment.animalsShowLessMortalMindLessDisease
  , GenesisEvolutionCounterMoment.errorNoEntityPower
  , GenesisEvolutionCounterMoment.originManLikeOriginGod
  , GenesisEvolutionCounterMoment.creationSpiritualBasis
  , GenesisEvolutionCounterMoment.jesusRestoresVanishedManifestation
  , GenesisEvolutionCounterMoment.generaMaterialConcepts
  , GenesisEvolutionCounterMoment.formerThingsPassAway
  , GenesisEvolutionCounterMoment.christianPrivilegeFathomsScience
  , GenesisEvolutionCounterMoment.adamSleepAsDream
  , GenesisEvolutionCounterMoment.ontologyBeforePhysiology
  , GenesisEvolutionCounterMoment.birthThroesBelief
  , GenesisEvolutionCounterMoment.curseRemovedByMistEvaporation
  , GenesisEvolutionCounterMoment.manNeverBornNeverDying
  , GenesisEvolutionCounterMoment.firstGenesisStandardRestored
  ]

structure GenesisEvolutionCounter where
  materialEvolutionCountered : Bool
  mindOnlyProducer : Bool
  matterCannotTransmitMind : Bool
  ontologyOverPhysiology : Bool
  curseRemoved : Bool
  genesisClosed : Bool
deriving DecidableEq, Repr

def genesisEvolutionCounter : GenesisEvolutionCounter where
  materialEvolutionCountered := true
  mindOnlyProducer := true
  matterCannotTransmitMind := true
  ontologyOverPhysiology := true
  curseRemoved := true
  genesisClosed := true

theorem eddy_genesis_evolution_counter_witness :
    genesisEvolutionCounterTrace.length = 49
    ∧ genesisEvolutionCounterTrace.head? =
      some GenesisEvolutionCounterMoment.agassizOvumStrengthensQuestion
    ∧ genesisEvolutionCounterTrace.getLast? =
      some GenesisEvolutionCounterMoment.firstGenesisStandardRestored
    ∧ genesisEvolutionCounter.materialEvolutionCountered = true
    ∧ genesisEvolutionCounter.mindOnlyProducer = true
    ∧ genesisEvolutionCounter.matterCannotTransmitMind = true
    ∧ genesisEvolutionCounter.ontologyOverPhysiology = true
    ∧ genesisEvolutionCounter.curseRemoved = true
    ∧ genesisEvolutionCounter.genesisClosed = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyGenesisEvolutionCounterWitness
end Gnosis.Witnesses.Eddy
