import Init

namespace Gnosis.Witnesses.Eddy
namespace EddyApocalypseLittleBookDragonWitness

/-!
# Science and Health, Chapter XVI -- Little Book, Woman, and Dragon

Source text: `docs/ebooks/source-texts/science-and-health-eddy.txt:22697-23280`.

Bounded section: 558:1-572:18. This Apocalypse unit interprets the little book
as divine Science, the woman as the spiritual idea, the dragon as the sum of
human error, and the warfare of Michael, Gabriel, Truth, Love, and the Lamb as
the reduction of sin to nothingness.
-/

inductive ApocalypseDragonMoment where
  | angelMessagePrefiguresScience
  | littleBookOpenToRead
  | truthVoiceArousesThunders
  | bookSweetAndBitter
  | revelationTwelfthPresentAge
  | heavenAsHarmony
  | messengerMustBeRightlyEstimated
  | persecutionHidesDivineIdea
  | womanBrideLambCorrelation
  | humanDivineCoincidence
  | womanGenericSpiritualIdea
  | moonUnderFeet
  | twelveStarsCrownHealing
  | travailBirthsPromise
  | dragonSumHumanError
  | hornsMatterPowerClaim
  | serpentStingsTruthHeel
  | animalInstinctDevours
  | dragonWarsInnocence
  | serpentFromGenesisToApocalypse
  | manChildRulesByScience
  | ideaCaughtUpToPrinciple
  | womanWildernessGuidance
  | sciencePillarCloudFire
  | michaelSpiritualStrength
  | gabrielMinisteringLove
  | truthLovePrevail
  | dragonCastDownDust
  | lambSlaysWolf
  | trueWarfareThenFalse
  | paeanVictoryOverSin
  | selfAbnegationRule
  | errorTemporal
  | occultismEventuallyChained
  | earthHelpsWoman
  | receptiveHeartsNeedWater
  | evilHiddenWaysExposed
  | warnAgainstFoe
  | overcomeEvilWithGood
  | revelatorMirrorRebukesSin
  | sinReducedToNothingness
  | loveFulfillsLaw
deriving DecidableEq, Repr

def apocalypseDragonTrace : List ApocalypseDragonMoment :=
  [ ApocalypseDragonMoment.angelMessagePrefiguresScience
  , ApocalypseDragonMoment.littleBookOpenToRead
  , ApocalypseDragonMoment.truthVoiceArousesThunders
  , ApocalypseDragonMoment.bookSweetAndBitter
  , ApocalypseDragonMoment.revelationTwelfthPresentAge
  , ApocalypseDragonMoment.heavenAsHarmony
  , ApocalypseDragonMoment.messengerMustBeRightlyEstimated
  , ApocalypseDragonMoment.persecutionHidesDivineIdea
  , ApocalypseDragonMoment.womanBrideLambCorrelation
  , ApocalypseDragonMoment.humanDivineCoincidence
  , ApocalypseDragonMoment.womanGenericSpiritualIdea
  , ApocalypseDragonMoment.moonUnderFeet
  , ApocalypseDragonMoment.twelveStarsCrownHealing
  , ApocalypseDragonMoment.travailBirthsPromise
  , ApocalypseDragonMoment.dragonSumHumanError
  , ApocalypseDragonMoment.hornsMatterPowerClaim
  , ApocalypseDragonMoment.serpentStingsTruthHeel
  , ApocalypseDragonMoment.animalInstinctDevours
  , ApocalypseDragonMoment.dragonWarsInnocence
  , ApocalypseDragonMoment.serpentFromGenesisToApocalypse
  , ApocalypseDragonMoment.manChildRulesByScience
  , ApocalypseDragonMoment.ideaCaughtUpToPrinciple
  , ApocalypseDragonMoment.womanWildernessGuidance
  , ApocalypseDragonMoment.sciencePillarCloudFire
  , ApocalypseDragonMoment.michaelSpiritualStrength
  , ApocalypseDragonMoment.gabrielMinisteringLove
  , ApocalypseDragonMoment.truthLovePrevail
  , ApocalypseDragonMoment.dragonCastDownDust
  , ApocalypseDragonMoment.lambSlaysWolf
  , ApocalypseDragonMoment.trueWarfareThenFalse
  , ApocalypseDragonMoment.paeanVictoryOverSin
  , ApocalypseDragonMoment.selfAbnegationRule
  , ApocalypseDragonMoment.errorTemporal
  , ApocalypseDragonMoment.occultismEventuallyChained
  , ApocalypseDragonMoment.earthHelpsWoman
  , ApocalypseDragonMoment.receptiveHeartsNeedWater
  , ApocalypseDragonMoment.evilHiddenWaysExposed
  , ApocalypseDragonMoment.warnAgainstFoe
  , ApocalypseDragonMoment.overcomeEvilWithGood
  , ApocalypseDragonMoment.revelatorMirrorRebukesSin
  , ApocalypseDragonMoment.sinReducedToNothingness
  , ApocalypseDragonMoment.loveFulfillsLaw
  ]

structure ApocalypseDragon where
  littleBookScience : Bool
  womanSpiritualIdea : Bool
  dragonHumanError : Bool
  truthLovePrevail : Bool
  sinReducedNothingness : Bool
deriving DecidableEq, Repr

def apocalypseDragon : ApocalypseDragon where
  littleBookScience := true
  womanSpiritualIdea := true
  dragonHumanError := true
  truthLovePrevail := true
  sinReducedNothingness := true

theorem eddy_apocalypse_little_book_dragon_witness :
    apocalypseDragonTrace.length = 42
    ∧ apocalypseDragonTrace.head? =
      some ApocalypseDragonMoment.angelMessagePrefiguresScience
    ∧ apocalypseDragonTrace.getLast? =
      some ApocalypseDragonMoment.loveFulfillsLaw
    ∧ apocalypseDragon.littleBookScience = true
    ∧ apocalypseDragon.womanSpiritualIdea = true
    ∧ apocalypseDragon.dragonHumanError = true
    ∧ apocalypseDragon.truthLovePrevail = true
    ∧ apocalypseDragon.sinReducedNothingness = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EddyApocalypseLittleBookDragonWitness
end Gnosis.Witnesses.Eddy
