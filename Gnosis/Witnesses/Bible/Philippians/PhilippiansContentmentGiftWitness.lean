import Init

namespace Gnosis.Witnesses.Bible.Philippians
namespace PhilippiansContentmentGiftWitness

/-!
# Philippians 4:10-23 -- Contentment, Gift Fruit, and Supplied Need

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94594-94641`.

The gift ledger is not greed for support. Paul names learned contentment across
abasing and abounding, then treats their giving as fruit to their account and a
well-pleasing sacrifice.

No `sorry`, no new `axiom`.
-/

structure ContentmentStrength where
  careFlourishedAgain : Bool := true
  learnedContentmentAnyState : Bool := true
  abasedAndAboundKnown : Bool := true
  fullHungryAboundNeed : Bool := true
  allThingsThroughStrengtheningChrist : Bool := true
deriving DecidableEq, Repr

def contentmentStrength : ContentmentStrength := {}

def contentmentStrengthWitness (c : ContentmentStrength) : Prop :=
  c.careFlourishedAgain = true ∧ c.learnedContentmentAnyState = true ∧
  c.abasedAndAboundKnown = true ∧ c.fullHungryAboundNeed = true ∧
  c.allThingsThroughStrengtheningChrist = true

structure GiftSupplyClosing where
  communicatedWithAffliction : Bool := true
  givingReceivingOnlyChurch : Bool := true
  sentOnceAgainToNecessity : Bool := true
  fruitAboundsToAccount : Bool := true
  giftAsSweetSacrifice : Bool := true
  godSuppliesNeedInGlory : Bool := true
  caesarHouseholdSaintsGreet : Bool := true
  graceClosing : Bool := true
deriving DecidableEq, Repr

def giftSupplyClosing : GiftSupplyClosing := {}

def giftSupplyWitness (g : GiftSupplyClosing) : Prop :=
  g.communicatedWithAffliction = true ∧ g.givingReceivingOnlyChurch = true ∧
  g.sentOnceAgainToNecessity = true ∧ g.fruitAboundsToAccount = true ∧
  g.giftAsSweetSacrifice = true ∧ g.godSuppliesNeedInGlory = true ∧
  g.caesarHouseholdSaintsGreet = true ∧ g.graceClosing = true

theorem philippians_contentment_strength :
    contentmentStrengthWitness contentmentStrength := by
  unfold contentmentStrengthWitness contentmentStrength
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem philippians_gift_supply :
    giftSupplyWitness giftSupplyClosing := by
  unfold giftSupplyWitness giftSupplyClosing
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem philippians_contentment_gift_witness :
    contentmentStrengthWitness contentmentStrength ∧ giftSupplyWitness giftSupplyClosing := by
  exact ⟨philippians_contentment_strength, philippians_gift_supply⟩

end PhilippiansContentmentGiftWitness
end Gnosis.Witnesses.Bible.Philippians
