import Init

namespace Gnosis.Witnesses.Bible.SecondCorinthians
namespace SecondCorinthiansCheerfulGivingWitness

/-! # 2 Corinthians 9 -- Cheerful Giving and Thanksgiving
Source text: `docs/ebooks/source-texts/bible-kjv.txt:93260-93301`. -/

structure CheerfulGiving where
  achaiaReadyZealProvokedMany : Bool
  brethrenSentToMakeBountyReady : Bool
  sowSparinglyBountifullyReapLikewise : Bool
  givePurposedNotGrudgingGodLovesCheerful : Bool
  graceAboundsAllSufficiencyGoodWork : Bool
  seedSowerBreadFoodFruitsRighteousness : Bool
  enrichedToBountifulnessThanksgiving : Bool
  serviceSuppliesSaintsAndThanksgivings : Bool
  ministrationGlorifiesGod : Bool
  thanksUnspeakableGift : Bool
deriving DecidableEq, Repr

def cheerfulGiving : CheerfulGiving where
  achaiaReadyZealProvokedMany := true
  brethrenSentToMakeBountyReady := true
  sowSparinglyBountifullyReapLikewise := true
  givePurposedNotGrudgingGodLovesCheerful := true
  graceAboundsAllSufficiencyGoodWork := true
  seedSowerBreadFoodFruitsRighteousness := true
  enrichedToBountifulnessThanksgiving := true
  serviceSuppliesSaintsAndThanksgivings := true
  ministrationGlorifiesGod := true
  thanksUnspeakableGift := true

theorem second_corinthians_cheerful_giving_witness :
    cheerfulGiving.achaiaReadyZealProvokedMany = true
    ∧ cheerfulGiving.brethrenSentToMakeBountyReady = true
    ∧ cheerfulGiving.sowSparinglyBountifullyReapLikewise = true
    ∧ cheerfulGiving.givePurposedNotGrudgingGodLovesCheerful = true
    ∧ cheerfulGiving.graceAboundsAllSufficiencyGoodWork = true
    ∧ cheerfulGiving.seedSowerBreadFoodFruitsRighteousness = true
    ∧ cheerfulGiving.enrichedToBountifulnessThanksgiving = true
    ∧ cheerfulGiving.serviceSuppliesSaintsAndThanksgivings = true
    ∧ cheerfulGiving.ministrationGlorifiesGod = true
    ∧ cheerfulGiving.thanksUnspeakableGift = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SecondCorinthiansCheerfulGivingWitness
end Gnosis.Witnesses.Bible.SecondCorinthians
