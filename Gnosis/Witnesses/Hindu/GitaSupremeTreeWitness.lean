import Gnosis.Witnesses.Hindu.GitaQualitiesSeparationWitness

namespace Gnosis.Witnesses.Hindu

/-! Witness ledger for `bhagavad-gita-arnold.txt`, chapter 15. -/

structure SupremeTree where
  invertedTreeRootAbove : Bool := true
  senseBranchesBelow : Bool := true
  detachmentAxeCutsRoots : Bool := true
  noReturnPlaceSought : Bool := true
  spiritEntersAndLeavesForms : Bool := true
  ignorantDoNotSeeDeparture : Bool := true
  sunMoonFireSplendourPointsToSource : Bool := true
  dividedUndividedSupremeLevels : Bool := true
  purushottamaBeyondBoth : Bool := true
deriving Repr, DecidableEq

def supremeTree : SupremeTree := {}

theorem gita_supreme_tree_witness :
    supremeTree.invertedTreeRootAbove = true ∧
      supremeTree.senseBranchesBelow = true ∧
      supremeTree.detachmentAxeCutsRoots = true ∧
      supremeTree.noReturnPlaceSought = true ∧
      supremeTree.spiritEntersAndLeavesForms = true ∧
      supremeTree.ignorantDoNotSeeDeparture = true ∧
      supremeTree.dividedUndividedSupremeLevels = true ∧
      supremeTree.purushottamaBeyondBoth = true := by
  simp [supremeTree]

end Gnosis.Witnesses.Hindu
