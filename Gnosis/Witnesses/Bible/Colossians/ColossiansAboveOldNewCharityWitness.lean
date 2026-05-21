import Init

namespace Gnosis.Witnesses.Bible.Colossians
namespace ColossiansAboveOldNewCharityWitness

/-!
# Colossians 3:1-17 -- Above-Affection, Old/New Man, and Charity Bond

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94808-94861`.

The risen-with-Christ premise moves affection upward, mortifies earthly members,
puts off the old man, puts on the new, and binds the virtues with charity and
peace.

No `sorry`, no new `axiom`.
-/

structure AboveHiddenLife where
  risenSeekAbove : Bool := true
  affectionAboveNotEarth : Bool := true
  deadLifeHiddenWithChrist : Bool := true
  appearWithChristInGlory : Bool := true
  earthlyMembersMortified : Bool := true
  wrathForDisobedienceNamed : Bool := true
deriving DecidableEq, Repr

def aboveHiddenLife : AboveHiddenLife := {}

def aboveHiddenLifeWitness (a : AboveHiddenLife) : Prop :=
  a.risenSeekAbove = true ∧ a.affectionAboveNotEarth = true ∧
  a.deadLifeHiddenWithChrist = true ∧ a.appearWithChristInGlory = true ∧
  a.earthlyMembersMortified = true ∧ a.wrathForDisobedienceNamed = true

structure OldNewCharity where
  angerSpeechLyingPutOff : Bool := true
  oldManPutOff : Bool := true
  newManPutOnRenewedKnowledge : Bool := true
  christAllAndInAll : Bool := true
  merciesKindnessHumilityMeekness : Bool := true
  forbearingForgivingAsChrist : Bool := true
  charityBondPerfectness : Bool := true
  peaceRulesOneBodyThankful : Bool := true
  wordDwellsRichlySongs : Bool := true
  allDoneInLordNameThanks : Bool := true
deriving DecidableEq, Repr

def oldNewCharity : OldNewCharity := {}

def oldNewCharityWitness (c : OldNewCharity) : Prop :=
  c.angerSpeechLyingPutOff = true ∧ c.oldManPutOff = true ∧
  c.newManPutOnRenewedKnowledge = true ∧ c.christAllAndInAll = true ∧
  c.merciesKindnessHumilityMeekness = true ∧ c.forbearingForgivingAsChrist = true ∧
  c.charityBondPerfectness = true ∧ c.peaceRulesOneBodyThankful = true ∧
  c.wordDwellsRichlySongs = true ∧ c.allDoneInLordNameThanks = true

theorem colossians_above_hidden_life :
    aboveHiddenLifeWitness aboveHiddenLife := by
  unfold aboveHiddenLifeWitness aboveHiddenLife
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem colossians_old_new_charity :
    oldNewCharityWitness oldNewCharity := by
  unfold oldNewCharityWitness oldNewCharity
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem colossians_above_old_new_charity_witness :
    aboveHiddenLifeWitness aboveHiddenLife ∧
    oldNewCharityWitness oldNewCharity := by
  exact ⟨colossians_above_hidden_life, colossians_old_new_charity⟩

end ColossiansAboveOldNewCharityWitness
end Gnosis.Witnesses.Bible.Colossians
