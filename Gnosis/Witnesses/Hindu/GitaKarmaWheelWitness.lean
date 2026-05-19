import Gnosis.Witnesses.Buddhist.DhammapadaAngerTripleControlWitness

namespace Gnosis.Witnesses.Hindu

/-! Witness ledger for `bhagavad-gita-arnold.txt`, chapter 3. -/

structure ActionUnavoidable where
  noEscapeByShunningAction : Bool := true
  natureCompelsAct : Bool := true
  thoughtCountsAsAct : Bool := true
  idleSenseThoughtHypocrisy : Bool := true
  worthyWorkWithoutGainHonourable : Bool := true
  allottedTaskRequired : Bool := true
deriving Repr, DecidableEq

structure SacrificeWorldWheel where
  workMoreExcellentThanIdleness : Bool := true
  sacrificeBindsNotFaithfulSoul : Bool := true
  foodRainSacrificeToilWheel : Bool := true
  selfishFeastEatsSin : Bool := true
  abstainingFromWorldWheelLostLife : Bool := true
  wiseActForWorldUpholding : Bool := true
deriving Repr, DecidableEq

structure DesireEnemy where
  qualitiesActEverywhere : Bool := true
  foolThinksThisIDid : Bool := true
  ownTaskBetterThanOtherTask : Bool := true
  passionPushesToIll : Bool := true
  desireSapsKnowledgeJudgment : Bool := true
  senseMindReasonAreBooty : Bool := true
  soulMustVanquishDoubtAndDesire : Bool := true
deriving Repr, DecidableEq

def actionUnavoidable : ActionUnavoidable := {}
def sacrificeWorldWheel : SacrificeWorldWheel := {}
def desireEnemy : DesireEnemy := {}

theorem gita_action_unavoidable :
    actionUnavoidable.noEscapeByShunningAction = true ∧
      actionUnavoidable.natureCompelsAct = true ∧
      actionUnavoidable.thoughtCountsAsAct = true ∧
      actionUnavoidable.idleSenseThoughtHypocrisy = true ∧
      actionUnavoidable.worthyWorkWithoutGainHonourable = true ∧
      actionUnavoidable.allottedTaskRequired = true := by
  simp [actionUnavoidable]

theorem gita_sacrifice_world_wheel :
    sacrificeWorldWheel.workMoreExcellentThanIdleness = true ∧
      sacrificeWorldWheel.sacrificeBindsNotFaithfulSoul = true ∧
      sacrificeWorldWheel.foodRainSacrificeToilWheel = true ∧
      sacrificeWorldWheel.selfishFeastEatsSin = true ∧
      sacrificeWorldWheel.abstainingFromWorldWheelLostLife = true ∧
      sacrificeWorldWheel.wiseActForWorldUpholding = true := by
  simp [sacrificeWorldWheel]

theorem gita_desire_enemy :
    desireEnemy.qualitiesActEverywhere = true ∧
      desireEnemy.foolThinksThisIDid = true ∧
      desireEnemy.ownTaskBetterThanOtherTask = true ∧
      desireEnemy.passionPushesToIll = true ∧
      desireEnemy.desireSapsKnowledgeJudgment = true ∧
      desireEnemy.senseMindReasonAreBooty = true ∧
      desireEnemy.soulMustVanquishDoubtAndDesire = true := by
  simp [desireEnemy]

theorem gita_karma_wheel_witness :
    actionUnavoidable.noEscapeByShunningAction = true ∧
      actionUnavoidable.idleSenseThoughtHypocrisy = true ∧
      sacrificeWorldWheel.foodRainSacrificeToilWheel = true ∧
      sacrificeWorldWheel.wiseActForWorldUpholding = true ∧
      desireEnemy.ownTaskBetterThanOtherTask = true ∧
      desireEnemy.desireSapsKnowledgeJudgment = true := by
  simp [actionUnavoidable, sacrificeWorldWheel, desireEnemy]

end Gnosis.Witnesses.Hindu
