import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyGenesisWomanCainWitness

/-!
# Science and Health, Chapter XV -- Woman, Cain, and Error's Mark

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:21720-22460`.

Bounded section: 531:12-546:30. This Genesis unit follows the Adamic dream into
woman's confession, the serpent prophecy, Cain and Abel, the mark of error,
material dreamland, man springing from Mind, material inception, mental tillage,
and healing proof as the authentication of spiritual interpretation.
-/

inductive GenesisWomanCainMoment where
  | womanConfessesFault
  | womanDiscernsCorporealSenseSerpent
  | womanFirstInterpretsScriptureSpiritually
  | sonOfVirginRemediesAdam
  | carnalMindEnmity
  | serpentBitesHeelWomanBruisesHead
  | wheatTaresSeparated
  | scienceDoomsMaterialFoundations
  | newEarthNoMoreSea
  | errorFallBlindLeadingBlind
  | passionsEndInPain
  | immortalReachedThroughStruggle
  | evilNoEssenceDivinity
  | errorExcludesItself
  | truthGuardsGateway
  | inspiredInterpretationAgainstLiteralism
  | treeLifeReality
  | treeKnowledgeUnreality
  | cainTemporalSinProgeny
  | falseOriginFratricidal
  | oneStandardGood
  | serpentLieCondemned
  | christOffspringSpirit
  | chemicalizationReducesEvil
  | renderCaesarAndGod
  | cainMaterialOffering
  | abelMindOffering
  | materialBeliefRupturesBrotherhood
  | brotherhoodRepudiated
  | murderBringsCurse
  | truthUnveilsError
  | justiceMarksSinner
  | errorClimaxesAndYields
  | realManNotEffaced
  | materialManDreamland
  | manSpringsFromMind
  | materialCreationApartFromGod
  | firstEvilSuggestionSerpent
  | materialPersonalityNotLikeness
  | mentalTillageDestroysMateriality
  | dustNothingnessReply
  | mortalityMyth
  | noTruthFromMaterialBasis
  | genesisApocalypseNeedSpiritualStandpoint
  | spiritualFactsDawning
  | healingProofAuthenticatesSystem
deriving DecidableEq, Repr

def genesisWomanCainTrace : List GenesisWomanCainMoment :=
  [ GenesisWomanCainMoment.womanConfessesFault
  , GenesisWomanCainMoment.womanDiscernsCorporealSenseSerpent
  , GenesisWomanCainMoment.womanFirstInterpretsScriptureSpiritually
  , GenesisWomanCainMoment.sonOfVirginRemediesAdam
  , GenesisWomanCainMoment.carnalMindEnmity
  , GenesisWomanCainMoment.serpentBitesHeelWomanBruisesHead
  , GenesisWomanCainMoment.wheatTaresSeparated
  , GenesisWomanCainMoment.scienceDoomsMaterialFoundations
  , GenesisWomanCainMoment.newEarthNoMoreSea
  , GenesisWomanCainMoment.errorFallBlindLeadingBlind
  , GenesisWomanCainMoment.passionsEndInPain
  , GenesisWomanCainMoment.immortalReachedThroughStruggle
  , GenesisWomanCainMoment.evilNoEssenceDivinity
  , GenesisWomanCainMoment.errorExcludesItself
  , GenesisWomanCainMoment.truthGuardsGateway
  , GenesisWomanCainMoment.inspiredInterpretationAgainstLiteralism
  , GenesisWomanCainMoment.treeLifeReality
  , GenesisWomanCainMoment.treeKnowledgeUnreality
  , GenesisWomanCainMoment.cainTemporalSinProgeny
  , GenesisWomanCainMoment.falseOriginFratricidal
  , GenesisWomanCainMoment.oneStandardGood
  , GenesisWomanCainMoment.serpentLieCondemned
  , GenesisWomanCainMoment.christOffspringSpirit
  , GenesisWomanCainMoment.chemicalizationReducesEvil
  , GenesisWomanCainMoment.renderCaesarAndGod
  , GenesisWomanCainMoment.cainMaterialOffering
  , GenesisWomanCainMoment.abelMindOffering
  , GenesisWomanCainMoment.materialBeliefRupturesBrotherhood
  , GenesisWomanCainMoment.brotherhoodRepudiated
  , GenesisWomanCainMoment.murderBringsCurse
  , GenesisWomanCainMoment.truthUnveilsError
  , GenesisWomanCainMoment.justiceMarksSinner
  , GenesisWomanCainMoment.errorClimaxesAndYields
  , GenesisWomanCainMoment.realManNotEffaced
  , GenesisWomanCainMoment.materialManDreamland
  , GenesisWomanCainMoment.manSpringsFromMind
  , GenesisWomanCainMoment.materialCreationApartFromGod
  , GenesisWomanCainMoment.firstEvilSuggestionSerpent
  , GenesisWomanCainMoment.materialPersonalityNotLikeness
  , GenesisWomanCainMoment.mentalTillageDestroysMateriality
  , GenesisWomanCainMoment.dustNothingnessReply
  , GenesisWomanCainMoment.mortalityMyth
  , GenesisWomanCainMoment.noTruthFromMaterialBasis
  , GenesisWomanCainMoment.genesisApocalypseNeedSpiritualStandpoint
  , GenesisWomanCainMoment.spiritualFactsDawning
  , GenesisWomanCainMoment.healingProofAuthenticatesSystem
  ]

structure GenesisWomanCain where
  womanDiscernsSerpent : Bool
  seedWarfareSeparatesTruthError : Bool
  cainMaterialBelief : Bool
  truthUnveilsError : Bool
  manSpringsFromMind : Bool
  dustMeansNothingness : Bool
  healingAuthenticatesReading : Bool
deriving DecidableEq, Repr

def genesisWomanCain : GenesisWomanCain where
  womanDiscernsSerpent := true
  seedWarfareSeparatesTruthError := true
  cainMaterialBelief := true
  truthUnveilsError := true
  manSpringsFromMind := true
  dustMeansNothingness := true
  healingAuthenticatesReading := true

theorem eddy_genesis_woman_cain_witness :
    genesisWomanCainTrace.length = 46
    ∧ genesisWomanCainTrace.head? =
      some GenesisWomanCainMoment.womanConfessesFault
    ∧ genesisWomanCainTrace.getLast? =
      some GenesisWomanCainMoment.healingProofAuthenticatesSystem
    ∧ genesisWomanCain.womanDiscernsSerpent = true
    ∧ genesisWomanCain.seedWarfareSeparatesTruthError = true
    ∧ genesisWomanCain.cainMaterialBelief = true
    ∧ genesisWomanCain.truthUnveilsError = true
    ∧ genesisWomanCain.manSpringsFromMind = true
    ∧ genesisWomanCain.dustMeansNothingness = true
    ∧ genesisWomanCain.healingAuthenticatesReading = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyGenesisWomanCainWitness
end Gnosis.Witnesses.Eddy
