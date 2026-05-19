import Gnosis.Witnesses.Hermetic.KybalionDivineParadoxWitness

namespace Gnosis.Witnesses.Hermetic

/-! Witness ledger for `kybalion-three-initiates.txt`, chapter 7. -/

structure AllInAll where
  allInTheAll : Bool := true
  theAllInAll : Bool := true
  paradoxReconcilesBoth : Bool := true
  immanentMindGivesVitality : Bool := true
  creatureNotIdenticalWithCreator : Bool := true
  iamTheAllOverclaimRejected : Bool := true
  progressAsReturningHome : Bool := true
  involutionOutpouring : Bool := true
  evolutionIndrawing : Bool := true
  whyQuestionExceedsAnswer : Bool := true
  closedLipsMarkBoundary : Bool := true
deriving Repr, DecidableEq

def allInAll : AllInAll := {}

theorem kybalion_all_in_all_witness :
    allInAll.allInTheAll = true ∧
      allInAll.theAllInAll = true ∧
      allInAll.paradoxReconcilesBoth = true ∧
      allInAll.immanentMindGivesVitality = true ∧
      allInAll.creatureNotIdenticalWithCreator = true ∧
      allInAll.iamTheAllOverclaimRejected = true ∧
      allInAll.progressAsReturningHome = true ∧
      allInAll.whyQuestionExceedsAnswer = true ∧
      allInAll.closedLipsMarkBoundary = true := by
  simp [allInAll]

end Gnosis.Witnesses.Hermetic
