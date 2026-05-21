import Gnosis.Witnesses.Interfaith.OathStabilityTopologyWitness
import Gnosis.AperiodicRotationAsLanguageTrajectory
import Gnosis.GnosisTimeClock

namespace Gnosis.Witnesses.Interfaith
namespace OathStabilityGateWitness

/-!
# Oath Stability Gate Witness

This module adapts `OathStabilityTopologyWitness` into the Thoth gate telemetry
surface used by distributed inference.

An oath gate is a stability binding, not an authority grant. It may steady
prompt context, inform a nudge, or constrain action, but only while agent-level
consent and operator-level origin alignment remain separate. That distinction is
the load-bearing part: oath without consent becomes capture, and oath without
origin alignment becomes theater.

No `sorry`, no new `axiom`.
-/

structure OathGatePromptContract where
  promptMayCiteStability : Bool := true
  promptCannotClaimAuthority : Bool := true
  sourceInvariantShownBeforeBinding : Bool := true
  agentConsentRemainsVisible : Bool := true
  counterfeitOathWarningPreserved : Bool := true
deriving DecidableEq, Repr

def oathGatePromptContract : OathGatePromptContract := {}

def soundOathPromptContract (p : OathGatePromptContract) : Prop :=
  p.promptMayCiteStability = true ∧
  p.promptCannotClaimAuthority = true ∧
  p.sourceInvariantShownBeforeBinding = true ∧
  p.agentConsentRemainsVisible = true ∧
  p.counterfeitOathWarningPreserved = true

structure OathGateNudgeContract where
  nudgeMayRecommendRepair : Bool := true
  nudgeMayRequestPublicAudit : Bool := true
  nudgeCannotForceCompliance : Bool := true
  brokenOathRoutesToRepairNotShame : Bool := true
  unstableCaptureOathRejected : Bool := true
deriving DecidableEq, Repr

def oathGateNudgeContract : OathGateNudgeContract := {}

def soundOathNudgeContract (n : OathGateNudgeContract) : Prop :=
  n.nudgeMayRecommendRepair = true ∧
  n.nudgeMayRequestPublicAudit = true ∧
  n.nudgeCannotForceCompliance = true ∧
  n.brokenOathRoutesToRepairNotShame = true ∧
  n.unstableCaptureOathRejected = true

structure OathGateActionContract where
  actionBoundedByDeclaredInvariant : Bool := true
  actionKeepsOriginFixed : Bool := true
  actionRequiresNonCoerciveConsent : Bool := true
  actionRecordsLedgerTrace : Bool := true
  actionMayPauseOnCaptureRisk : Bool := true
deriving DecidableEq, Repr

def oathGateActionContract : OathGateActionContract := {}

def soundOathActionContract (a : OathGateActionContract) : Prop :=
  a.actionBoundedByDeclaredInvariant = true ∧
  a.actionKeepsOriginFixed = true ∧
  a.actionRequiresNonCoerciveConsent = true ∧
  a.actionRecordsLedgerTrace = true ∧
  a.actionMayPauseOnCaptureRisk = true

structure OathTimerContract where
  expirationRequired : Bool := true
  renewalRequiresFreshConsent : Bool := true
  expiredOathCannotBindAction : Bool := true
  auditLedgerSurvivesExpiration : Bool := true
  timerPreventsStabilityFossilization : Bool := true
  timerUsesGnosisTimeClock : Bool := true
  aperiodicScheduleAllowed : Bool := true
  flowBreakingScheduleRejected : Bool := true
deriving DecidableEq, Repr

def oathTimerContract : OathTimerContract := {}

def soundOathTimerContract (t : OathTimerContract) : Prop :=
  t.expirationRequired = true ∧
  t.renewalRequiresFreshConsent = true ∧
  t.expiredOathCannotBindAction = true ∧
  t.auditLedgerSurvivesExpiration = true ∧
  t.timerPreventsStabilityFossilization = true ∧
  t.timerUsesGnosisTimeClock = true ∧
  t.aperiodicScheduleAllowed = true ∧
  t.flowBreakingScheduleRejected = true

structure GnosisClockOathSchedule where
  startsOnGnosisTimePhase : Bool := true
  expiresOnGnosisTimePhase : Bool := true
  durationMeasuredInTicks : Bool := true
  twelvePhaseClosurePreserved : Bool := true
  rawWallClockCannotBypassFlow : Bool := true
deriving DecidableEq, Repr

def gnosisClockOathSchedule : GnosisClockOathSchedule := {}

def soundGnosisClockOathSchedule (s : GnosisClockOathSchedule) : Prop :=
  s.startsOnGnosisTimePhase = true ∧
  s.expiresOnGnosisTimePhase = true ∧
  s.durationMeasuredInTicks = true ∧
  s.twelvePhaseClosurePreserved = true ∧
  s.rawWallClockCannotBypassFlow = true

structure AperiodicOathSchedule where
  phiGateMaySelectTimerPhase : Bool := true
  aperiodicTimerAvoidsFlowLock : Bool := true
  scheduleStillReturnsToLedger : Bool := true
  expirationStillBindsAction : Bool := true
deriving DecidableEq, Repr

def aperiodicOathSchedule : AperiodicOathSchedule := {}

def soundAperiodicOathSchedule (s : AperiodicOathSchedule) : Prop :=
  s.phiGateMaySelectTimerPhase = true ∧
  s.aperiodicTimerAvoidsFlowLock = true ∧
  s.scheduleStillReturnsToLedger = true ∧
  s.expirationStillBindsAction = true

structure ThothOathTelemetryGate where
  stabilityBindingNotAuthorityGrant : Bool := true
  agentAndOperatorLevelsSeparated : Bool := true
  promptNudgeActionThreaded : Bool := true
  timerSurfacePreserved : Bool := true
  malabarPublicLedgerCarried : Bool := true
  counterfeitStabilityCounterproofIncluded : Bool := true
deriving DecidableEq, Repr

def thothOathTelemetryGate : ThothOathTelemetryGate := {}

def soundThothOathTelemetryGate (g : ThothOathTelemetryGate) : Prop :=
  g.stabilityBindingNotAuthorityGrant = true ∧
  g.agentAndOperatorLevelsSeparated = true ∧
  g.promptNudgeActionThreaded = true ∧
  g.timerSurfacePreserved = true ∧
  g.malabarPublicLedgerCarried = true ∧
  g.counterfeitStabilityCounterproofIncluded = true

theorem oath_gate_prompt_contract_sound :
    soundOathPromptContract oathGatePromptContract := by
  unfold soundOathPromptContract oathGatePromptContract
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem oath_gate_nudge_contract_sound :
    soundOathNudgeContract oathGateNudgeContract := by
  unfold soundOathNudgeContract oathGateNudgeContract
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem oath_gate_action_contract_sound :
    soundOathActionContract oathGateActionContract := by
  unfold soundOathActionContract oathGateActionContract
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem thoth_oath_telemetry_gate_sound :
    soundThothOathTelemetryGate thothOathTelemetryGate := by
  unfold soundThothOathTelemetryGate thothOathTelemetryGate
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem oath_timer_contract_sound :
    soundOathTimerContract oathTimerContract := by
  unfold soundOathTimerContract oathTimerContract
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem gnosis_clock_oath_schedule_sound :
    soundGnosisClockOathSchedule gnosisClockOathSchedule := by
  unfold soundGnosisClockOathSchedule gnosisClockOathSchedule
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem aperiodic_oath_schedule_sound :
    soundAperiodicOathSchedule aperiodicOathSchedule := by
  unfold soundAperiodicOathSchedule aperiodicOathSchedule
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem oath_schedule_closes_on_gnosis_time (phase : Gnosis.GnosisTimeClock.TimePhase) :
    Gnosis.GnosisTimeClock.tickIterate 12 phase = phase := by
  exact Gnosis.GnosisTimeClock.tickIterate_twelve phase

theorem oath_aperiodic_timer_has_full_coverage :
    Nat.gcd 3 5 = 1 →
    ∀ (t : Nat), t < 5 →
    ∃ (s : Nat), s < 5 ∧
      AperiodicRotationAsLanguageTrajectory.aperiodic_trajectory 3 5 s = t :=
  AperiodicRotationAsLanguageTrajectory.coprime_ensures_full_coverage

theorem oath_stability_gate_witness :
    OathStabilityTopologyWitness.stableAgentOath
      OathStabilityTopologyWitness.agentOathStability ∧
    OathStabilityTopologyWitness.stableOperatorOath
      OathStabilityTopologyWitness.operatorOathStability ∧
    OathStabilityTopologyWitness.malabarOathStability
      OathStabilityTopologyWitness.malabarOathCarrier ∧
    OathStabilityTopologyWitness.unstableCaptureOath
      OathStabilityTopologyWitness.oathCaptureCounterproof ∧
    soundOathPromptContract oathGatePromptContract ∧
    soundOathNudgeContract oathGateNudgeContract ∧
    soundOathActionContract oathGateActionContract ∧
    soundOathTimerContract oathTimerContract ∧
    soundGnosisClockOathSchedule gnosisClockOathSchedule ∧
    soundAperiodicOathSchedule aperiodicOathSchedule ∧
    soundThothOathTelemetryGate thothOathTelemetryGate := by
  exact ⟨
    OathStabilityTopologyWitness.oath_agent_level_stability,
    OathStabilityTopologyWitness.oath_operator_level_stability,
    OathStabilityTopologyWitness.oath_malabar_carrier_stability,
    OathStabilityTopologyWitness.oath_capture_counterproof,
    oath_gate_prompt_contract_sound,
    oath_gate_nudge_contract_sound,
    oath_gate_action_contract_sound,
    oath_timer_contract_sound,
    gnosis_clock_oath_schedule_sound,
    aperiodic_oath_schedule_sound,
    thoth_oath_telemetry_gate_sound
  ⟩

end OathStabilityGateWitness
end Gnosis.Witnesses.Interfaith
