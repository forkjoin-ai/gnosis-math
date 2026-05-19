import Gnosis.BuddhistAttachmentSkyrms

namespace Gnosis.Witnesses.Buddhist

/-! Witness ledger for Dhammapada chapter 24, "Thirst". -/

structure ThirstCreeper where
  thoughtlessThirstGrowsLikeCreeper : Bool := true
  thirstOvercomeIncreasesSuffering : Bool := true
  thirstOvercomeDropsSufferingLikeLotusWater : Bool := true
  rootOfThirstDugUp : Bool := true
  rootSafePainReturns : Bool := true
  channelsEverywhere : Bool := true
  rootCutByKnowledge : Bool := true
deriving Repr, DecidableEq

structure FetterStream where
  thirstDrivesLikeSnaredHare : Bool := true
  freedOneRunningBackToForestReturnsBondage : Bool := true
  familyTreasureFetterStrongerThanIron : Bool := true
  spiderWebSelfMadePassionStream : Bool := true
  beforeBehindMiddleGivenUp : Bool := true
  freeMindNoBirthDecayReturn : Bool := true
deriving Repr, DecidableEq

structure LastBodyLawGift where
  doubtsPassionsStrengthenFetters : Bool := true
  reflectionOnNotDelightfulCutsMaraFetter : Bool := true
  noThirstNoSinLastBody : Bool := true
  lawGiftExceedsAllGifts : Bool := true
  thirstExtinctionOvercomesAllPain : Bool := true
  pleasureThirstDestroysFool : Bool := true
  passionsHatredVanityLustDamageFields : Bool := true
deriving Repr, DecidableEq

def thirstCreeper : ThirstCreeper := {}
def fetterStream : FetterStream := {}
def lastBodyLawGift : LastBodyLawGift := {}

theorem dhammapada_thirst_creeper :
    thirstCreeper.thoughtlessThirstGrowsLikeCreeper = true ∧
      thirstCreeper.thirstOvercomeIncreasesSuffering = true ∧
      thirstCreeper.thirstOvercomeDropsSufferingLikeLotusWater = true ∧
      thirstCreeper.rootOfThirstDugUp = true ∧
      thirstCreeper.rootSafePainReturns = true ∧
      thirstCreeper.channelsEverywhere = true ∧
      thirstCreeper.rootCutByKnowledge = true := by
  simp [thirstCreeper]

theorem dhammapada_fetter_stream :
    fetterStream.thirstDrivesLikeSnaredHare = true ∧
      fetterStream.freedOneRunningBackToForestReturnsBondage = true ∧
      fetterStream.familyTreasureFetterStrongerThanIron = true ∧
      fetterStream.spiderWebSelfMadePassionStream = true ∧
      fetterStream.beforeBehindMiddleGivenUp = true ∧
      fetterStream.freeMindNoBirthDecayReturn = true := by
  simp [fetterStream]

theorem dhammapada_last_body_law_gift :
    lastBodyLawGift.doubtsPassionsStrengthenFetters = true ∧
      lastBodyLawGift.reflectionOnNotDelightfulCutsMaraFetter = true ∧
      lastBodyLawGift.noThirstNoSinLastBody = true ∧
      lastBodyLawGift.lawGiftExceedsAllGifts = true ∧
      lastBodyLawGift.thirstExtinctionOvercomesAllPain = true ∧
      lastBodyLawGift.pleasureThirstDestroysFool = true ∧
      lastBodyLawGift.passionsHatredVanityLustDamageFields = true := by
  simp [lastBodyLawGift]

theorem dhammapada_thirst_root_cut_witness :
    thirstCreeper.rootOfThirstDugUp = true ∧
      thirstCreeper.rootCutByKnowledge = true ∧
      fetterStream.freedOneRunningBackToForestReturnsBondage = true ∧
      fetterStream.freeMindNoBirthDecayReturn = true ∧
      lastBodyLawGift.noThirstNoSinLastBody = true ∧
      lastBodyLawGift.thirstExtinctionOvercomesAllPain = true := by
  simp [thirstCreeper, fetterStream, lastBodyLawGift]

end Gnosis.Witnesses.Buddhist
