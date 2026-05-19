import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Hindu

/-! Witness ledger for `bhagavad-gita-arnold.txt`, chapter 9. -/

structure KinglyMystery where
  royalLoreFreesFromIlls : Bool := true
  allContainedYetNotContainingSource : Bool := true
  creationSustainedWithoutAttachment : Bool := true
  untaughtMistakeVeiledForm : Bool := true
  oneSpiritManifold : Bool := true
  witnessRefugeFriendFountainSea : Bool := true
  deathAndImmortalLife : Bool := true
  satAndAsatVisibleInvisible : Bool := true
  meritHeavenReturnsToChange : Bool := true
  leafFlowerFruitAccepted : Bool := true
  allActsOfferedBreakKarmaBond : Bool := true
  nonePerishTrusting : Bool := true
deriving Repr, DecidableEq

def kinglyMystery : KinglyMystery := {}

theorem gita_kingly_mystery_witness :
    kinglyMystery.royalLoreFreesFromIlls = true ∧
      kinglyMystery.allContainedYetNotContainingSource = true ∧
      kinglyMystery.creationSustainedWithoutAttachment = true ∧
      kinglyMystery.witnessRefugeFriendFountainSea = true ∧
      kinglyMystery.satAndAsatVisibleInvisible = true ∧
      kinglyMystery.meritHeavenReturnsToChange = true ∧
      kinglyMystery.allActsOfferedBreakKarmaBond = true ∧
      kinglyMystery.nonePerishTrusting = true := by
  simp [kinglyMystery]

end Gnosis.Witnesses.Hindu
