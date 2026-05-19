import Gnosis.BuddhistAttachmentSkyrms

namespace Gnosis.Witnesses.Buddhist

/-! Witness ledger for Dhammapada chapter 16, "Pleasure". -/

structure PleasureGriefFear where
  vanityDisplacesMeditation : Bool := true
  realAimForgotten : Bool := true
  loveNothingHateNothingNoFetters : Bool := true
  pleasureGeneratesGriefFear : Bool := true
  affectionGeneratesGriefFear : Bool := true
  lustGeneratesGriefFear : Bool := true
  loveGeneratesGriefFear : Bool := true
  greedGeneratesGriefFear : Bool := true
  freedomRemovesGriefFear : Bool := true
  thoughtsNotBewilderedByLove : Bool := true
deriving Repr, DecidableEq

def pleasureGriefFear : PleasureGriefFear := {}

theorem dhammapada_pleasure_grief_fear_witness :
    pleasureGriefFear.vanityDisplacesMeditation = true ∧
      pleasureGriefFear.realAimForgotten = true ∧
      pleasureGriefFear.loveNothingHateNothingNoFetters = true ∧
      pleasureGriefFear.pleasureGeneratesGriefFear = true ∧
      pleasureGriefFear.greedGeneratesGriefFear = true ∧
      pleasureGriefFear.freedomRemovesGriefFear = true ∧
      pleasureGriefFear.thoughtsNotBewilderedByLove = true := by
  simp [pleasureGriefFear]

end Gnosis.Witnesses.Buddhist
