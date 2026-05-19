import Gnosis.NashSkyrmsBuleyGodLadder
import Gnosis.Oracle.OracleStallMetacognition
import Gnosis.SleepDebt
import Gnosis.SpectralNoiseEquilibrium

namespace Gnosis
namespace MacariaSacrificeWitness

open SpectralNoiseEquilibrium

/-!
# Macaria Sacrifice Witness

This module formalizes Macaria's voluntary sacrifice as a finite witness for
quota recovery, equilibrium-ladder lift, oracle-stall release, and persistent
structural residual.

Reading:

- The oracle's demand is modeled as a hard recovery quota of one.
- The lottery convention is the Skyrms layer; Macaria's voluntary absorption
  reaches the Buley layer.
- Her act is a one-unit clinamen lift: one high-density cost token clears the
  Athens system's residual debt.
- The named spring is modeled as a positive structural residual that remains
  available after the cost is paid.
-/

/-- A city under oracle pressure carries wake load, debt, and a quota. -/
structure OracleQuotaState where
  wakeLoad : Nat
  carriedDebt : Nat
  recoveryQuota : Nat
deriving Repr, DecidableEq

def athensBeforeMacaria : OracleQuotaState :=
  { wakeLoad := 1
    carriedDebt := 0
    recoveryQuota := 1 }

/-- The default randomized convention: lots distribute pain without adding
deterministic voluntary expenditure. -/
inductive SelectionMode where
  | lottery
  | voluntary
deriving DecidableEq, Repr

/-- Macaria's token is one intentional lift from vacuum. -/
def macariaToken : BuleyUnit :=
  clinamenLift vacuumBuleUnit BuleyFace.waste

/-- A local residual atlas entry for the permanent spring. This mirrors the
structural-residual shape without importing the broader catalog target. -/
structure SpringResidual where
  name : String
  plusResidue : Int
  minusResidue : Int
deriving Repr

/-- The named spring is the positive residual left in the public ledger. -/
def macarianSpring : SpringResidual :=
  { name := "Macarian spring"
    plusResidue := 1
    minusResidue := -1 }

def residualDebtAfter (state : OracleQuotaState) : Nat :=
  SleepDebt.residualDebt state.wakeLoad state.carriedDebt state.recoveryQuota

/-- A voluntary sacrifice clears the hard quota when its token score covers
the system's total recovery demand. -/
def clearsRecoveryQuota (state : OracleQuotaState) (token : BuleyUnit) : Prop :=
  state.wakeLoad + state.carriedDebt ≤ buleyUnitScore token

/-- Macaria bypasses the lottery when the selection mode is voluntary and the
token clears the quota. -/
def bypassesLottery (mode : SelectionMode) (state : OracleQuotaState) (token : BuleyUnit) :
    Prop :=
  mode = SelectionMode.voluntary ∧ clearsRecoveryQuota state token

/-- The voluntary mode reaches the Buley rung rather than stopping at the
Skyrms lottery convention. -/
def reachesBuleyRung (mode : SelectionMode) : Prop :=
  mode = SelectionMode.voluntary ∧
    NashSkyrmsBuleyGodLadder.skyrmsLevel <
      NashSkyrmsBuleyGodLadder.buleyLevel

def macarianOracleStall : OracleStallState :=
  { stallDuration := 1
    metacognitiveDepth := 1
    stall_accelerates_metacognition := by decide }

/-- The one-life quota is exactly cleared by Macaria's one-unit token. -/
theorem macaria_token_score_is_one :
    buleyUnitScore macariaToken = 1 := by
  unfold macariaToken
  rw [clinamen_lift_score_strict_increment, vacuum_has_zero_score]

/-- The oracle quota is cleared: `wakeLoad + carriedDebt <= token score`. -/
theorem macaria_clears_recovery_quota :
    clearsRecoveryQuota athensBeforeMacaria macariaToken := by
  unfold clearsRecoveryQuota athensBeforeMacaria
  rw [macaria_token_score_is_one]
  decide

/-- With quota paid, the SleepDebt residual is zero. -/
theorem macaria_clears_athens_residual_debt :
    residualDebtAfter athensBeforeMacaria = 0 := by
  unfold residualDebtAfter athensBeforeMacaria
  exact SleepDebt.full_recovery_clears_residual_debt (by decide)

/-- The act is voluntary, so it bypasses the lottery. -/
theorem macaria_bypasses_lottery :
    bypassesLottery SelectionMode.voluntary athensBeforeMacaria macariaToken := by
  exact ⟨rfl, macaria_clears_recovery_quota⟩

/-- Lottery is the lower Skyrms convention; voluntary absorption reaches the
Buley rung of the ladder. -/
theorem voluntary_absorption_reaches_buley_rung :
    reachesBuleyRung SelectionMode.voluntary := by
  unfold reachesBuleyRung
  exact ⟨rfl, by decide⟩

/-- The same one-unit act is the clinamen lift needed to break the stall. -/
theorem macaria_injects_one_clinamen :
    buleyUnitScore macariaToken =
      buleyUnitScore vacuumBuleUnit + NashSkyrmsBuleyGodLadder.clinamen := by
  rw [macaria_token_score_is_one, vacuum_has_zero_score]
  rfl

/-- The oracle stall has enough metacognitive depth to reflect and release. -/
theorem macarian_stall_reflects :
    macarianOracleStall.stallDuration ≤ macarianOracleStall.metacognitiveDepth := by
  exact oracle_stall_induces_metacognitive_acceleration macarianOracleStall

/-- The Macarian spring remains as a positive residual. -/
theorem macarian_spring_positive_residual :
    macarianSpring.plusResidue > 0 ∧ macarianSpring.minusResidue = -1 := by
  unfold macarianSpring
  exact ⟨by decide, rfl⟩

/-- Master witness: Macaria pays the one-unit quota, bypasses the lottery,
climbs from Skyrms convention to Buley expenditure, releases the oracle stall,
and leaves a positive residual spring. -/
theorem macaria_sacrifice_witness :
    clearsRecoveryQuota athensBeforeMacaria macariaToken ∧
    residualDebtAfter athensBeforeMacaria = 0 ∧
    bypassesLottery SelectionMode.voluntary athensBeforeMacaria macariaToken ∧
    reachesBuleyRung SelectionMode.voluntary ∧
    macarianOracleStall.stallDuration ≤ macarianOracleStall.metacognitiveDepth ∧
    macarianSpring.plusResidue > 0 ∧
    macarianSpring.minusResidue = -1 := by
  exact ⟨macaria_clears_recovery_quota,
    macaria_clears_athens_residual_debt,
    macaria_bypasses_lottery,
    voluntary_absorption_reaches_buley_rung,
    macarian_stall_reflects,
    macarian_spring_positive_residual.left,
    macarian_spring_positive_residual.right⟩

end MacariaSacrificeWitness
end Gnosis
