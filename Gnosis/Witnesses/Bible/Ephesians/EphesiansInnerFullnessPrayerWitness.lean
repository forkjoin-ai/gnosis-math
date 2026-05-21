import Init

namespace Gnosis.Witnesses.Bible.Ephesians
namespace EphesiansInnerFullnessPrayerWitness

/-!
# Ephesians 3:14-21 -- Inner Strength, Fourfold Comprehension, and Fullness

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94132-94151`.

The prayer asks for inner strengthening, indwelling, rooted love, impossible
comprehension, and fullness. It ends by naming the power at work in us as beyond
ask-or-think capacity.

No `sorry`, no new `axiom`.
-/

structure InnerFullnessPrayer where
  kneesBowedToFather : Bool := true
  familyInHeavenEarthNamed : Bool := true
  strengthenedBySpiritInnerMan : Bool := true
  christDwellsByFaith : Bool := true
  rootedGroundedInLove : Bool := true
  breadthLengthDepthHeightComprehended : Bool := true
  lovePassingKnowledgeKnown : Bool := true
  filledWithFullnessOfGod : Bool := true
  exceedingAbundantlyAboveAsked : Bool := true
  gloryInChurchAllAges : Bool := true
deriving DecidableEq, Repr

def innerFullnessPrayer : InnerFullnessPrayer := {}

def innerFullnessWitness (p : InnerFullnessPrayer) : Prop :=
  p.kneesBowedToFather = true ∧ p.familyInHeavenEarthNamed = true ∧
  p.strengthenedBySpiritInnerMan = true ∧ p.christDwellsByFaith = true ∧
  p.rootedGroundedInLove = true ∧ p.breadthLengthDepthHeightComprehended = true ∧
  p.lovePassingKnowledgeKnown = true ∧ p.filledWithFullnessOfGod = true ∧
  p.exceedingAbundantlyAboveAsked = true ∧ p.gloryInChurchAllAges = true

theorem ephesians_inner_fullness :
    innerFullnessWitness innerFullnessPrayer := by
  unfold innerFullnessWitness innerFullnessPrayer
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EphesiansInnerFullnessPrayerWitness
end Gnosis.Witnesses.Bible.Ephesians
