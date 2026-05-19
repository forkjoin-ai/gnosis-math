import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Hindu

/-! Witness ledger for `bhagavad-gita-arnold.txt`, chapter 7. -/

structure DiscernmentVeil where
  lowerNatureEightfold : Bool := true
  higherLifePrinciple : Bool := true
  worldsHangLikePearlsOnString : Bool := true
  qualitiesAriseFromSource : Bool := true
  sourceNotMergedInQualities : Bool := true
  threeQualitiesVeilEternal : Bool := true
  worshipPiercesVeil : Bool := true
  lowerWorshipFruitWithers : Bool := true
  likeDislikeBewilderCreatures : Bool := true
  deathHourHolding : Bool := true
deriving Repr, DecidableEq

def discernmentVeil : DiscernmentVeil := {}

theorem gita_discernment_veil_witness :
    discernmentVeil.lowerNatureEightfold = true ∧
      discernmentVeil.higherLifePrinciple = true ∧
      discernmentVeil.worldsHangLikePearlsOnString = true ∧
      discernmentVeil.sourceNotMergedInQualities = true ∧
      discernmentVeil.threeQualitiesVeilEternal = true ∧
      discernmentVeil.worshipPiercesVeil = true ∧
      discernmentVeil.lowerWorshipFruitWithers = true ∧
      discernmentVeil.likeDislikeBewilderCreatures = true ∧
      discernmentVeil.deathHourHolding = true := by
  simp [discernmentVeil]

end Gnosis.Witnesses.Hindu
