import Gnosis.Witnesses.Buddhist.DhammapadaSelfRefugeWitness

namespace Gnosis.Witnesses.Hindu

/-! Witness ledger for `bhagavad-gita-arnold.txt`, chapter 6. -/

structure SelfFriendEnemy where
  workWithoutGainMakesSanyasiYogi : Bool := true
  workAsWorshipRaisesFaith : Bool := true
  resultSetAside : Bool := true
  selfRaisedBySoul : Bool := true
  selfNotTrampled : Bool := true
  selfFriendWhenSelfRulesSelf : Bool := true
  selfEnemyWhenSelfNotRuled : Bool := true
deriving Repr, DecidableEq

structure ModeratePractice where
  pleasurePainHeatColdGloryShameAlike : Bool := true
  clodRockGoldSame : Bool := true
  equalGraceToFriendEnemyKin : Bool := true
  solitaryMeditationControlledThoughts : Bool := true
  tooMuchFastFeastSleepVigilRejected : Bool := true
  moderationRemovesEarthAches : Bool := true
  lampShelteredFromWind : Bool := true
deriving Repr, DecidableEq

structure MindReturnYoga where
  griefCannotShakePeace : Bool := true
  senseDoorwaysShut : Bool := true
  mindRecurbedToSoulGovernance : Bool := true
  lifeSoulSeenInAll : Bool := true
  allSeenInLifeSoul : Bool := true
  oneEssenceInEvilAndGood : Bool := true
  heartRestrainedByHabit : Bool := true
  failedRightDesireNotLost : Bool := true
deriving Repr, DecidableEq

def selfFriendEnemy : SelfFriendEnemy := {}
def moderatePractice : ModeratePractice := {}
def mindReturnYoga : MindReturnYoga := {}

theorem gita_self_friend_enemy :
    selfFriendEnemy.workWithoutGainMakesSanyasiYogi = true ∧
      selfFriendEnemy.workAsWorshipRaisesFaith = true ∧
      selfFriendEnemy.resultSetAside = true ∧
      selfFriendEnemy.selfRaisedBySoul = true ∧
      selfFriendEnemy.selfNotTrampled = true ∧
      selfFriendEnemy.selfFriendWhenSelfRulesSelf = true ∧
      selfFriendEnemy.selfEnemyWhenSelfNotRuled = true := by
  simp [selfFriendEnemy]

theorem gita_moderate_practice :
    moderatePractice.pleasurePainHeatColdGloryShameAlike = true ∧
      moderatePractice.clodRockGoldSame = true ∧
      moderatePractice.equalGraceToFriendEnemyKin = true ∧
      moderatePractice.solitaryMeditationControlledThoughts = true ∧
      moderatePractice.tooMuchFastFeastSleepVigilRejected = true ∧
      moderatePractice.moderationRemovesEarthAches = true ∧
      moderatePractice.lampShelteredFromWind = true := by
  simp [moderatePractice]

theorem gita_mind_return_yoga :
    mindReturnYoga.griefCannotShakePeace = true ∧
      mindReturnYoga.senseDoorwaysShut = true ∧
      mindReturnYoga.mindRecurbedToSoulGovernance = true ∧
      mindReturnYoga.lifeSoulSeenInAll = true ∧
      mindReturnYoga.allSeenInLifeSoul = true ∧
      mindReturnYoga.oneEssenceInEvilAndGood = true ∧
      mindReturnYoga.heartRestrainedByHabit = true ∧
      mindReturnYoga.failedRightDesireNotLost = true := by
  simp [mindReturnYoga]

theorem gita_self_restraint_witness :
    selfFriendEnemy.selfFriendWhenSelfRulesSelf = true ∧
      selfFriendEnemy.selfEnemyWhenSelfNotRuled = true ∧
      moderatePractice.tooMuchFastFeastSleepVigilRejected = true ∧
      moderatePractice.lampShelteredFromWind = true ∧
      mindReturnYoga.mindRecurbedToSoulGovernance = true ∧
      mindReturnYoga.lifeSoulSeenInAll = true ∧
      mindReturnYoga.failedRightDesireNotLost = true := by
  simp [selfFriendEnemy, moderatePractice, mindReturnYoga]

end Gnosis.Witnesses.Hindu
