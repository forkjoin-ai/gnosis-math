import Init

namespace Gnosis.Witnesses.Bible.Colossians
namespace ColossiansFruitTransferChristologyWitness

/-!
# Colossians 1:1-20 -- Fruitful Gospel, Transfer, and Cosmic Christology

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94642-94704`.

Colossians opens with gospel fruit and then expands into cosmic Christology:
delivered from darkness, translated into the Son's kingdom, all things created
by and for him, and all fullness dwelling in him.

No `sorry`, no new `axiom`.
-/

structure FruitfulGospelPrayer where
  saintsFaithfulAddressed : Bool := true
  faithLoveHopeHeard : Bool := true
  wordTruthGospelFruit : Bool := true
  epaphrasFaithfulMinister : Bool := true
  filledWithWillWisdomUnderstanding : Bool := true
  worthyFruitfulWalk : Bool := true
  strengthenedPatienceJoy : Bool := true
deriving DecidableEq, Repr

def fruitfulGospelPrayer : FruitfulGospelPrayer := {}

def fruitfulPrayerWitness (p : FruitfulGospelPrayer) : Prop :=
  p.saintsFaithfulAddressed = true ∧ p.faithLoveHopeHeard = true ∧
  p.wordTruthGospelFruit = true ∧ p.epaphrasFaithfulMinister = true ∧
  p.filledWithWillWisdomUnderstanding = true ∧ p.worthyFruitfulWalk = true ∧
  p.strengthenedPatienceJoy = true

structure TransferChristology where
  madeMeetInheritanceLight : Bool := true
  deliveredFromDarkness : Bool := true
  translatedToSonKingdom : Bool := true
  redemptionForgivenessBlood : Bool := true
  imageInvisibleGod : Bool := true
  allThingsCreatedByForHim : Bool := true
  beforeAllThingsConsist : Bool := true
  headBodyBeginningFirstbornDead : Bool := true
  allFullnessDwells : Bool := true
  peaceAndReconciliationByCrossBlood : Bool := true
deriving DecidableEq, Repr

def transferChristology : TransferChristology := {}

def transferChristologyWitness (c : TransferChristology) : Prop :=
  c.madeMeetInheritanceLight = true ∧ c.deliveredFromDarkness = true ∧
  c.translatedToSonKingdom = true ∧ c.redemptionForgivenessBlood = true ∧
  c.imageInvisibleGod = true ∧ c.allThingsCreatedByForHim = true ∧
  c.beforeAllThingsConsist = true ∧ c.headBodyBeginningFirstbornDead = true ∧
  c.allFullnessDwells = true ∧ c.peaceAndReconciliationByCrossBlood = true

theorem colossians_fruitful_prayer :
    fruitfulPrayerWitness fruitfulGospelPrayer := by
  unfold fruitfulPrayerWitness fruitfulGospelPrayer
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem colossians_transfer_christology :
    transferChristologyWitness transferChristology := by
  unfold transferChristologyWitness transferChristology
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem colossians_fruit_transfer_christology_witness :
    fruitfulPrayerWitness fruitfulGospelPrayer ∧
    transferChristologyWitness transferChristology := by
  exact ⟨colossians_fruitful_prayer, colossians_transfer_christology⟩

end ColossiansFruitTransferChristologyWitness
end Gnosis.Witnesses.Bible.Colossians
