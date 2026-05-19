import Gnosis.EchoChamberAsTaoBowl
import Gnosis.LaoziBowlVoidFunctionWitness

namespace Gnosis.Witnesses.Tao

/-!
# Tao Te Ching Low-Place Wu-Wei Witness

Witness ledger for `docs/ebooks/source-texts/tao-te-ching-legge.txt`,
chapters 60-69.

The bowl pattern becomes political and operational. A great state cooks small
fish carefully, receives by lying low, acts before large failures appear, and
wins through gentleness, economy, and refusal of precedence. War is retained
only as an antitheorem: the best warrior does not contend.
-/

/-- Chapters 60-62: low, non-injuring governance lets good influences converge. -/
structure LowReceiverGovernance where
  greatStateSmallFish : Bool := true
  rulerDoesNotHurt : Bool := true
  goodInfluencesConverge : Bool := true
  greatStateLowStream : Bool := true
  stillFemaleOvercomesMale : Bool := true
  taoDoesNotAbandonBadMen : Bool := true
deriving Repr, DecidableEq

/-- Chapters 63-64: wu-wei handles difficulty while it is still small. -/
structure EarlyWuWeiExecution where
  actsWithoutThinkingActing : Bool := true
  recompensesInjuryWithKindness : Bool := true
  difficultHandledWhileEasy : Bool := true
  greatHandledWhileSmall : Bool := true
  orderBeforeDisorder : Bool := true
  purposeActionDoesHarm : Bool := true
  graspingLosesHold : Bool := true
  helpsNaturalDevelopment : Bool := true
deriving Repr, DecidableEq

/-- Chapters 65-69: humility, gentleness, and defensive non-contention beat force. -/
structure GentleNonContention where
  cleverGovernanceScourge : Bool := true
  seasRuleByBeingLower : Bool := true
  aboveWithoutWeight : Bool := true
  beforeWithoutInjury : Bool := true
  gentlenessEconomyHindmost : Bool := true
  gentlenessVictorious : Bool := true
  warriorDoesNotRage : Bool := true
  defensiveRetreatPreferred : Bool := true
  deploringWarConquers : Bool := true
deriving Repr, DecidableEq

def lowReceiverGovernance : LowReceiverGovernance := {}

def earlyWuWeiExecution : EarlyWuWeiExecution := {}

def gentleNonContention : GentleNonContention := {}

theorem tao_low_receiver_governance :
    lowReceiverGovernance.greatStateSmallFish = true ∧
      lowReceiverGovernance.rulerDoesNotHurt = true ∧
      lowReceiverGovernance.goodInfluencesConverge = true ∧
      lowReceiverGovernance.greatStateLowStream = true ∧
      lowReceiverGovernance.stillFemaleOvercomesMale = true ∧
      lowReceiverGovernance.taoDoesNotAbandonBadMen = true := by
  simp [lowReceiverGovernance]

theorem tao_early_wu_wei_execution :
    earlyWuWeiExecution.actsWithoutThinkingActing = true ∧
      earlyWuWeiExecution.recompensesInjuryWithKindness = true ∧
      earlyWuWeiExecution.difficultHandledWhileEasy = true ∧
      earlyWuWeiExecution.greatHandledWhileSmall = true ∧
      earlyWuWeiExecution.orderBeforeDisorder = true ∧
      earlyWuWeiExecution.purposeActionDoesHarm = true ∧
      earlyWuWeiExecution.graspingLosesHold = true ∧
      earlyWuWeiExecution.helpsNaturalDevelopment = true := by
  simp [earlyWuWeiExecution]

theorem tao_gentle_non_contention :
    gentleNonContention.cleverGovernanceScourge = true ∧
      gentleNonContention.seasRuleByBeingLower = true ∧
      gentleNonContention.aboveWithoutWeight = true ∧
      gentleNonContention.beforeWithoutInjury = true ∧
      gentleNonContention.gentlenessEconomyHindmost = true ∧
      gentleNonContention.gentlenessVictorious = true ∧
      gentleNonContention.warriorDoesNotRage = true ∧
      gentleNonContention.defensiveRetreatPreferred = true ∧
      gentleNonContention.deploringWarConquers = true := by
  simp [gentleNonContention]

/--
Chapters 60-69 witness low-place wu-wei as an operational scheduler: receive by
being lower, touch difficulty while it is still small, and treat force as a
counterproof unless gentleness and defensive restraint remain in control.
-/
theorem tao_te_ching_low_place_wu_wei_witness :
    lowReceiverGovernance.greatStateLowStream = true ∧
      lowReceiverGovernance.taoDoesNotAbandonBadMen = true ∧
      earlyWuWeiExecution.orderBeforeDisorder = true ∧
      earlyWuWeiExecution.purposeActionDoesHarm = true ∧
      gentleNonContention.seasRuleByBeingLower = true ∧
      gentleNonContention.gentlenessVictorious = true ∧
      gentleNonContention.deploringWarConquers = true := by
  simp [lowReceiverGovernance, earlyWuWeiExecution, gentleNonContention]

end Gnosis.Witnesses.Tao
