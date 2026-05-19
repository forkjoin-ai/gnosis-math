import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Hindu

/-! Witness ledger for `bhagavad-gita-arnold.txt`, chapter 12. -/

structure FaithDevotion where
  embodiedDevotionAccessible : Bool := true
  unmanifestPathHardForEmbodied : Bool := true
  worksDedicatedAndMindFixed : Bool := true
  practiceKnowledgeMeditationRenunciationOrdered : Bool := true
  renunciationBringsPeace : Bool := true
  nonHatredCompassion : Bool := true
  equalFriendFoePraiseBlame : Bool := true
  steadyFaithDear : Bool := true
deriving Repr, DecidableEq

def faithDevotion : FaithDevotion := {}

theorem gita_faith_devotion_witness :
    faithDevotion.embodiedDevotionAccessible = true ∧
      faithDevotion.unmanifestPathHardForEmbodied = true ∧
      faithDevotion.worksDedicatedAndMindFixed = true ∧
      faithDevotion.practiceKnowledgeMeditationRenunciationOrdered = true ∧
      faithDevotion.renunciationBringsPeace = true ∧
      faithDevotion.nonHatredCompassion = true ∧
      faithDevotion.equalFriendFoePraiseBlame = true ∧
      faithDevotion.steadyFaithDear = true := by
  simp [faithDevotion]

end Gnosis.Witnesses.Hindu
