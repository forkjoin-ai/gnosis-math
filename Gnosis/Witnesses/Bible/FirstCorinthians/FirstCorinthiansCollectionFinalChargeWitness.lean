import Init

namespace Gnosis.Witnesses.Bible.FirstCorinthians
namespace FirstCorinthiansCollectionFinalChargeWitness

/-! # 1 Corinthians 16 -- Collection, Travel, Watchfulness, and Final Greetings
Source text: `docs/ebooks/source-texts/bible-kjv.txt:92737-92802`. -/

structure CollectionFinalCharge where
  collectionFirstDayAsProspered : Bool
  approvedLettersToJerusalem : Bool
  travelThroughMacedoniaAndEphesus : Bool
  effectualDoorManyAdversaries : Bool
  timotheusAndApollosCare : Bool
  watchStandFastQuitStrongCharity : Bool
  houseOfStephanasAddictedMinistry : Bool
  finalSalutationsAndHolyKiss : Bool
  anathemaIfLoveNotLord : Bool
  graceAndLoveInChrist : Bool
deriving DecidableEq, Repr

def collectionFinalCharge : CollectionFinalCharge where
  collectionFirstDayAsProspered := true
  approvedLettersToJerusalem := true
  travelThroughMacedoniaAndEphesus := true
  effectualDoorManyAdversaries := true
  timotheusAndApollosCare := true
  watchStandFastQuitStrongCharity := true
  houseOfStephanasAddictedMinistry := true
  finalSalutationsAndHolyKiss := true
  anathemaIfLoveNotLord := true
  graceAndLoveInChrist := true

theorem first_corinthians_collection_final_charge_witness :
    collectionFinalCharge.collectionFirstDayAsProspered = true
    ∧ collectionFinalCharge.approvedLettersToJerusalem = true
    ∧ collectionFinalCharge.travelThroughMacedoniaAndEphesus = true
    ∧ collectionFinalCharge.effectualDoorManyAdversaries = true
    ∧ collectionFinalCharge.timotheusAndApollosCare = true
    ∧ collectionFinalCharge.watchStandFastQuitStrongCharity = true
    ∧ collectionFinalCharge.houseOfStephanasAddictedMinistry = true
    ∧ collectionFinalCharge.finalSalutationsAndHolyKiss = true
    ∧ collectionFinalCharge.anathemaIfLoveNotLord = true
    ∧ collectionFinalCharge.graceAndLoveInChrist = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FirstCorinthiansCollectionFinalChargeWitness
end Gnosis.Witnesses.Bible.FirstCorinthians
