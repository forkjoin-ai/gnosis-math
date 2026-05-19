import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Hermetic

/-! Witness ledger for `kybalion-three-initiates.txt`, chapter 4. -/

structure TheAllUnknowable where
  changeImpliesSubstantialReality : Bool := true
  allBeyondTrueNaming : Bool := true
  essenceUnknowable : Bool := true
  theologyAnthropomorphismRejected : Bool := true
  reasonReportsRespected : Bool := true
  allInfiniteAbsoluteEternal : Bool := true
  allImmutableInRealNature : Bool := true
  matterEnergyInsufficient : Bool := true
  infiniteLivingMind : Bool := true
deriving Repr, DecidableEq

def theAllUnknowable : TheAllUnknowable := {}

theorem kybalion_all_unknowable_witness :
    theAllUnknowable.changeImpliesSubstantialReality = true ∧
      theAllUnknowable.allBeyondTrueNaming = true ∧
      theAllUnknowable.essenceUnknowable = true ∧
      theAllUnknowable.theologyAnthropomorphismRejected = true ∧
      theAllUnknowable.reasonReportsRespected = true ∧
      theAllUnknowable.allInfiniteAbsoluteEternal = true ∧
      theAllUnknowable.matterEnergyInsufficient = true ∧
      theAllUnknowable.infiniteLivingMind = true := by
  simp [theAllUnknowable]

end Gnosis.Witnesses.Hermetic
