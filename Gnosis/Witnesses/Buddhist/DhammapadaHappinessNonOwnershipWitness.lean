import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Buddhist

/-! Witness ledger for Dhammapada chapter 15, "Happiness". -/

structure HappinessNonOwnership where
  nonHatredAmongHaters : Bool := true
  greedFreeAmongGreedy : Bool := true
  nothingOwned : Bool := true
  victoryBreedsHatred : Bool := true
  victoryDefeatGivenUpHappy : Bool := true
  restHighestHappiness : Bool := true
  nirvanaHighestHappiness : Bool := true
  solitudeTranquillitySweet : Bool := true
  wiseCompanyPleasure : Bool := true
deriving Repr, DecidableEq

def happinessNonOwnership : HappinessNonOwnership := {}

theorem dhammapada_happiness_non_ownership_witness :
    happinessNonOwnership.nonHatredAmongHaters = true ∧
      happinessNonOwnership.greedFreeAmongGreedy = true ∧
      happinessNonOwnership.nothingOwned = true ∧
      happinessNonOwnership.victoryBreedsHatred = true ∧
      happinessNonOwnership.victoryDefeatGivenUpHappy = true ∧
      happinessNonOwnership.restHighestHappiness = true ∧
      happinessNonOwnership.wiseCompanyPleasure = true := by
  simp [happinessNonOwnership]

end Gnosis.Witnesses.Buddhist
