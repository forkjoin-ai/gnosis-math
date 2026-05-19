import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyGlossarySpiritualDefinitionsWitness

/-!
# Science and Health, Chapter XVII -- Spiritual Definitions

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:23499-24207`.

Bounded section: 579:1-599:6. The glossary is an alphabetic witness ledger:
Scriptural terms are translated from material definition into spiritual sense,
with repeated forks between Spirit/Mind/Love and matter/error/mortal belief.
-/

inductive GlossaryMoment where
  | spiritualDefinitionsExplainScripture
  | abelWatchfulness
  | abrahamFaithLifePrinciple
  | adamErrorNothingness
  | adversaryLiarOpposer
  | angelsGodThoughts
  | arkSafetyTruthReflection
  | babelSelfDestroyingError
  | baptismPurificationSpirit
  | bridePuritySoulSense
  | churchStructureTruthLove
  | creatorSpiritMindLifeTruthLove
  | danAnimalMagnetism
  | dayIrradianceTruthLove
  | deathIllusionOppositeLife
  | devilEvilLieError
  | dustNothingness
  | earthCompoundIdea
  | eliasProphecyScience
  | euphratesScienceEncompassingUniverse
  | eveMaterialOriginBelief
  | firmamentDemarcationTruthError
  | gethsemaneHumanYieldingDivine
  | godGreatIAm
  | godsFiniteMindTheories
  | goodOmniAction
  | heavenHarmonySpiritGovernment
  | hellMortalBeliefSelfDestruction
  | holyGhostDivineScience
  | egoOnePrinciple
  | jacobSenseYieldingScience
  | jerusalemMortalBeliefAndHomeHeaven
  | jesusHighestHumanConceptDivineIdea
  | kingdomHarmonyRealmMind
  | knowledgeCorporealEvidence
  | lambLoveInnocenceSacrifice
  | lordGodJehovahSecondRecord
  | manCompoundIdeaSpirit
  | matterMortalMindIllusion
  | mindOnlyIPrinciple
  | miracleDivinelyNatural
  | mortalMindNothingClaimingSomething
  | motherGodPrinciple
  | newJerusalemDivineScience
  | oilConsecrationCharity
  | prophetSpiritualSeer
  | redDragonErrorFearAnimalMagnetism
  | resurrectionSpiritualizationThought
  | riverChannelThought
  | rockSpiritualFoundation
  | salvationLifeTruthLoveDemonstrated
  | serpentFirstLieLimitation
  | spiritDivineSubstance
  | sunSoulSymbol
  | templeBodyOrTruthStructure
  | timeMortalMeasurement
  | unknownKnownBySpiritualSense
  | urimSpiritIllumination
  | valleyIlluminedByLifeLove
  | veilHypocrisyRentByScience
  | wildernessVestibuleSenseDisappears
  | willMortalBeliefOrGodQuality
  | windPneumaSpiritTerm
  | wineInspirationOrTemptation
  | yearForetasteEternity
  | zionSpiritualFoundation
deriving DecidableEq, Repr

def glossaryTrace : List GlossaryMoment :=
  [ GlossaryMoment.spiritualDefinitionsExplainScripture
  , GlossaryMoment.abelWatchfulness
  , GlossaryMoment.abrahamFaithLifePrinciple
  , GlossaryMoment.adamErrorNothingness
  , GlossaryMoment.adversaryLiarOpposer
  , GlossaryMoment.angelsGodThoughts
  , GlossaryMoment.arkSafetyTruthReflection
  , GlossaryMoment.babelSelfDestroyingError
  , GlossaryMoment.baptismPurificationSpirit
  , GlossaryMoment.bridePuritySoulSense
  , GlossaryMoment.churchStructureTruthLove
  , GlossaryMoment.creatorSpiritMindLifeTruthLove
  , GlossaryMoment.danAnimalMagnetism
  , GlossaryMoment.dayIrradianceTruthLove
  , GlossaryMoment.deathIllusionOppositeLife
  , GlossaryMoment.devilEvilLieError
  , GlossaryMoment.dustNothingness
  , GlossaryMoment.earthCompoundIdea
  , GlossaryMoment.eliasProphecyScience
  , GlossaryMoment.euphratesScienceEncompassingUniverse
  , GlossaryMoment.eveMaterialOriginBelief
  , GlossaryMoment.firmamentDemarcationTruthError
  , GlossaryMoment.gethsemaneHumanYieldingDivine
  , GlossaryMoment.godGreatIAm
  , GlossaryMoment.godsFiniteMindTheories
  , GlossaryMoment.goodOmniAction
  , GlossaryMoment.heavenHarmonySpiritGovernment
  , GlossaryMoment.hellMortalBeliefSelfDestruction
  , GlossaryMoment.holyGhostDivineScience
  , GlossaryMoment.egoOnePrinciple
  , GlossaryMoment.jacobSenseYieldingScience
  , GlossaryMoment.jerusalemMortalBeliefAndHomeHeaven
  , GlossaryMoment.jesusHighestHumanConceptDivineIdea
  , GlossaryMoment.kingdomHarmonyRealmMind
  , GlossaryMoment.knowledgeCorporealEvidence
  , GlossaryMoment.lambLoveInnocenceSacrifice
  , GlossaryMoment.lordGodJehovahSecondRecord
  , GlossaryMoment.manCompoundIdeaSpirit
  , GlossaryMoment.matterMortalMindIllusion
  , GlossaryMoment.mindOnlyIPrinciple
  , GlossaryMoment.miracleDivinelyNatural
  , GlossaryMoment.mortalMindNothingClaimingSomething
  , GlossaryMoment.motherGodPrinciple
  , GlossaryMoment.newJerusalemDivineScience
  , GlossaryMoment.oilConsecrationCharity
  , GlossaryMoment.prophetSpiritualSeer
  , GlossaryMoment.redDragonErrorFearAnimalMagnetism
  , GlossaryMoment.resurrectionSpiritualizationThought
  , GlossaryMoment.riverChannelThought
  , GlossaryMoment.rockSpiritualFoundation
  , GlossaryMoment.salvationLifeTruthLoveDemonstrated
  , GlossaryMoment.serpentFirstLieLimitation
  , GlossaryMoment.spiritDivineSubstance
  , GlossaryMoment.sunSoulSymbol
  , GlossaryMoment.templeBodyOrTruthStructure
  , GlossaryMoment.timeMortalMeasurement
  , GlossaryMoment.unknownKnownBySpiritualSense
  , GlossaryMoment.urimSpiritIllumination
  , GlossaryMoment.valleyIlluminedByLifeLove
  , GlossaryMoment.veilHypocrisyRentByScience
  , GlossaryMoment.wildernessVestibuleSenseDisappears
  , GlossaryMoment.willMortalBeliefOrGodQuality
  , GlossaryMoment.windPneumaSpiritTerm
  , GlossaryMoment.wineInspirationOrTemptation
  , GlossaryMoment.yearForetasteEternity
  , GlossaryMoment.zionSpiritualFoundation
  ]

structure GlossarySpiritualDefinitions where
  materialTermsTranslated : Bool
  adamErrorNothingness : Bool
  godMindLovePrinciple : Bool
  matterMortalMindIllusion : Bool
  manCompoundIdea : Bool
  serpentFirstLie : Bool
  loveScienceGlossaryClosure : Bool
deriving DecidableEq, Repr

def glossarySpiritualDefinitions : GlossarySpiritualDefinitions where
  materialTermsTranslated := true
  adamErrorNothingness := true
  godMindLovePrinciple := true
  matterMortalMindIllusion := true
  manCompoundIdea := true
  serpentFirstLie := true
  loveScienceGlossaryClosure := true

theorem eddy_glossary_spiritual_definitions_witness :
    glossaryTrace.length = 66
    ∧ glossaryTrace.head? =
      some GlossaryMoment.spiritualDefinitionsExplainScripture
    ∧ glossaryTrace.getLast? =
      some GlossaryMoment.zionSpiritualFoundation
    ∧ glossarySpiritualDefinitions.materialTermsTranslated = true
    ∧ glossarySpiritualDefinitions.adamErrorNothingness = true
    ∧ glossarySpiritualDefinitions.godMindLovePrinciple = true
    ∧ glossarySpiritualDefinitions.matterMortalMindIllusion = true
    ∧ glossarySpiritualDefinitions.manCompoundIdea = true
    ∧ glossarySpiritualDefinitions.serpentFirstLie = true
    ∧ glossarySpiritualDefinitions.loveScienceGlossaryClosure = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyGlossarySpiritualDefinitionsWitness
end Gnosis.Witnesses.Eddy
