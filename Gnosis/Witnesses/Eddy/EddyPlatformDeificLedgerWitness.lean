import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyPlatformDeificLedgerWitness

/-!
# Science and Health, Chapter X -- Platform I-XXI

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:13726-13980`.

Bounded section: 330:8-336:1. The numbered platform compresses the chapter's
metaphysical ledger: one Mind, evil obsolete, Life not confined to forms,
Spirit all-in-all, Christ as incorporeal idea, the Jesus/Christ distinction,
one Spirit, Spirit as only substance, and Mind as deathless Ego.
-/

inductive PlatformMoment where
  | letterSpiritBearWitness
  | godOnlyLifeSubstanceSpiritSoul
  | oneMindOnly
  | evilNothingClaimingSomething
  | lifeNotConfinedToForms
  | spiritAllInAll
  | godUniversalCauseOnlyCreator
  | triunePrinciple
  | fatherMotherTenderRelation
  | christTrueIdeaVoicingGood
  | comforterLeadsIntoTruth
  | jesusVirginSonHumanForm
  | christNotSynonymForJesus
  | christWithoutBeginningOrEnd
  | spiritualIdeaAntedatesAbraham
  | seenJesusAndUnseenChristDistinguished
  | christUndyingInMind
  | oneInfiniteSpirit
  | spiritOnlySubstance
  | soulSpiritOne
  | mindProducesNothingUnlikeGod
  | egoDeathlessLimitless
deriving DecidableEq, Repr

def platformTrace : List PlatformMoment :=
  [ PlatformMoment.letterSpiritBearWitness
  , PlatformMoment.godOnlyLifeSubstanceSpiritSoul
  , PlatformMoment.oneMindOnly
  , PlatformMoment.evilNothingClaimingSomething
  , PlatformMoment.lifeNotConfinedToForms
  , PlatformMoment.spiritAllInAll
  , PlatformMoment.godUniversalCauseOnlyCreator
  , PlatformMoment.triunePrinciple
  , PlatformMoment.fatherMotherTenderRelation
  , PlatformMoment.christTrueIdeaVoicingGood
  , PlatformMoment.comforterLeadsIntoTruth
  , PlatformMoment.jesusVirginSonHumanForm
  , PlatformMoment.christNotSynonymForJesus
  , PlatformMoment.christWithoutBeginningOrEnd
  , PlatformMoment.spiritualIdeaAntedatesAbraham
  , PlatformMoment.seenJesusAndUnseenChristDistinguished
  , PlatformMoment.christUndyingInMind
  , PlatformMoment.oneInfiniteSpirit
  , PlatformMoment.spiritOnlySubstance
  , PlatformMoment.soulSpiritOne
  , PlatformMoment.mindProducesNothingUnlikeGod
  , PlatformMoment.egoDeathlessLimitless
  ]

structure PlatformDeificLedger where
  oneMindOnly : Bool
  evilNoThingNoPower : Bool
  lifeNotInMatter : Bool
  allnessSpirit : Bool
  trinityInUnity : Bool
  christIncorporealIdea : Bool
  jesusChristDistinguished : Bool
  christEternal : Bool
  oneSpiritOnly : Bool
  spiritOnlySubstance : Bool
  soulSpiritOne : Bool
  egoDeathless : Bool
deriving DecidableEq, Repr

def platformDeificLedger : PlatformDeificLedger where
  oneMindOnly := true
  evilNoThingNoPower := true
  lifeNotInMatter := true
  allnessSpirit := true
  trinityInUnity := true
  christIncorporealIdea := true
  jesusChristDistinguished := true
  christEternal := true
  oneSpiritOnly := true
  spiritOnlySubstance := true
  soulSpiritOne := true
  egoDeathless := true

theorem eddy_platform_deific_ledger_witness :
    platformTrace.length = 22
    ∧ platformTrace.head? =
      some PlatformMoment.letterSpiritBearWitness
    ∧ platformTrace.getLast? =
      some PlatformMoment.egoDeathlessLimitless
    ∧ platformDeificLedger.oneMindOnly = true
    ∧ platformDeificLedger.evilNoThingNoPower = true
    ∧ platformDeificLedger.lifeNotInMatter = true
    ∧ platformDeificLedger.allnessSpirit = true
    ∧ platformDeificLedger.trinityInUnity = true
    ∧ platformDeificLedger.christIncorporealIdea = true
    ∧ platformDeificLedger.jesusChristDistinguished = true
    ∧ platformDeificLedger.christEternal = true
    ∧ platformDeificLedger.oneSpiritOnly = true
    ∧ platformDeificLedger.spiritOnlySubstance = true
    ∧ platformDeificLedger.soulSpiritOne = true
    ∧ platformDeificLedger.egoDeathless = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyPlatformDeificLedgerWitness
end Gnosis.Witnesses.Eddy
