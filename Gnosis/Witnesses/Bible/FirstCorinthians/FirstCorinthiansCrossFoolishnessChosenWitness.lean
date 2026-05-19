import Init

namespace Gnosis.Witnesses.Bible.FirstCorinthians
namespace FirstCorinthiansCrossFoolishnessChosenWitness

/-!
# 1 Corinthians 1:18-31 -- Cross, Foolishness, and Chosen Things

Source text: `docs/ebooks/source-texts/bible-kjv.txt:91637-91669`.
-/

structure CrossFoolishnessChosen where
  crossFoolishToPerishingPowerToSaved : Bool
  godDestroysWisdomOfWise : Bool
  worldByWisdomKnewNotGod : Bool
  preachingSavesBelievers : Bool
  christCrucifiedStumblingblockAndFoolishness : Bool
  christPowerAndWisdomToCalled : Bool
  godChoseFoolishWeakBaseDespised : Bool
  noFleshGloriesInPresence : Bool
  christMadeWisdomRighteousnessSanctificationRedemption : Bool
  gloryInLord : Bool
deriving DecidableEq, Repr

def crossFoolishnessChosen : CrossFoolishnessChosen where
  crossFoolishToPerishingPowerToSaved := true
  godDestroysWisdomOfWise := true
  worldByWisdomKnewNotGod := true
  preachingSavesBelievers := true
  christCrucifiedStumblingblockAndFoolishness := true
  christPowerAndWisdomToCalled := true
  godChoseFoolishWeakBaseDespised := true
  noFleshGloriesInPresence := true
  christMadeWisdomRighteousnessSanctificationRedemption := true
  gloryInLord := true

theorem first_corinthians_cross_foolishness_chosen_witness :
    crossFoolishnessChosen.crossFoolishToPerishingPowerToSaved = true
    ∧ crossFoolishnessChosen.godDestroysWisdomOfWise = true
    ∧ crossFoolishnessChosen.worldByWisdomKnewNotGod = true
    ∧ crossFoolishnessChosen.preachingSavesBelievers = true
    ∧ crossFoolishnessChosen.christCrucifiedStumblingblockAndFoolishness = true
    ∧ crossFoolishnessChosen.christPowerAndWisdomToCalled = true
    ∧ crossFoolishnessChosen.godChoseFoolishWeakBaseDespised = true
    ∧ crossFoolishnessChosen.noFleshGloriesInPresence = true
    ∧ crossFoolishnessChosen.christMadeWisdomRighteousnessSanctificationRedemption = true
    ∧ crossFoolishnessChosen.gloryInLord = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FirstCorinthiansCrossFoolishnessChosenWitness
end Gnosis.Witnesses.Bible.FirstCorinthians
