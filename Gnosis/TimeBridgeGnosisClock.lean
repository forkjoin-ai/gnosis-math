import Gnosis.TimeBridgeWaveArches
import Gnosis.GnosisTimeClock

/-
  TimeBridgeGnosisClock.lean
  ==========================

  Places the time bridge on the existing twelve-phase Gnosis clock:

  * past-collapse sits at the predecessor phase,
  * present-defer sits at phase zero,
  * future-commit sits at the successor phase,
  * the three-step force monodromy preserves the carrier while the twelve-step
    clock closes every projected phase.
-/

namespace GnosisMath
namespace TimeBridgeGnosisClock

open Gnosis.GnosisTimeClock
open Gnosis.AeonCycleTwelveShadow
open GnosisMath.TimeBridgePresentCarrier
open GnosisMath.TimeBridgeTritonDynamics
open GnosisMath.TimeBridgeForceCycle
open GnosisMath.TimeBridgeWaveArches

/-- Project a bridge temporal dynamic to the twelve-phase Gnosis clock. -/
def timeBridgeClockPhase : TemporalDynamic → TimePhase
  | .pastCollapse => phaseOfNatTick 11
  | .presentDefer => phaseOfNatTick 0
  | .futureCommit => phaseOfNatTick 1

/-- Past-collapse is the predecessor clock face. -/
theorem past_collapse_clock_phase_value :
    (timeBridgeClockPhase TemporalDynamic.pastCollapse).val = 11 := by
  native_decide

/-- Present-defer is the zero clock face. -/
theorem present_defer_clock_phase_value :
    (timeBridgeClockPhase TemporalDynamic.presentDefer).val = 0 := by
  native_decide

/-- Future-commit is the successor clock face. -/
theorem future_commit_clock_phase_value :
    (timeBridgeClockPhase TemporalDynamic.futureCommit).val = 1 := by
  native_decide

/-- One clock tick carries present-defer to future-commit. -/
theorem present_tick_commits_future :
    tick (timeBridgeClockPhase TemporalDynamic.presentDefer) =
      timeBridgeClockPhase TemporalDynamic.futureCommit := by
  rfl

/-- One clock tick carries past-collapse into present-defer. -/
theorem past_tick_defers_present :
    tick (timeBridgeClockPhase TemporalDynamic.pastCollapse) =
      timeBridgeClockPhase TemporalDynamic.presentDefer := by
  rfl

/-- Twelve clock ticks close every bridge phase. -/
theorem twelve_ticks_close_bridge_phase (phase : TemporalDynamic) :
    tickIterate twelve (timeBridgeClockPhase phase) =
      timeBridgeClockPhase phase :=
  tickIterate_twelve (timeBridgeClockPhase phase)

/-- Three force-cycle steps preserve the projected clock phase. -/
theorem three_force_steps_preserve_clock_phase (phase : TemporalDynamic) :
    timeBridgeClockPhase (iterateTemporalDynamic 3 phase) =
      timeBridgeClockPhase phase := by
  rw [three_step_temporal_monodromy]

/-- The Gnosis clock projection keeps the same two-port carrier topology. -/
theorem gnosis_clock_projection_preserves_carrier (phase : TemporalDynamic) :
    dynamicCarrier phase = (timeBridgePresent.entry, timeBridgePresent.exit) := by
  cases phase <;> rfl

/--
  Clock bundle: the time bridge maps past/present/future dynamics to adjacent
  clock faces, the twelve-phase clock closes, the three-step force cycle closes,
  and the wave arch remains attached to the same carrier.
-/
theorem time_bridge_gnosis_clock_bundle :
    (timeBridgeClockPhase TemporalDynamic.pastCollapse).val = 11 ∧
    (timeBridgeClockPhase TemporalDynamic.presentDefer).val = 0 ∧
    (timeBridgeClockPhase TemporalDynamic.futureCommit).val = 1 ∧
    tick (timeBridgeClockPhase TemporalDynamic.pastCollapse) =
      timeBridgeClockPhase TemporalDynamic.presentDefer ∧
    tick (timeBridgeClockPhase TemporalDynamic.presentDefer) =
      timeBridgeClockPhase TemporalDynamic.futureCommit ∧
    (∀ phase : TemporalDynamic,
      tickIterate twelve (timeBridgeClockPhase phase) =
        timeBridgeClockPhase phase) ∧
    (∀ phase : TemporalDynamic,
      timeBridgeClockPhase (iterateTemporalDynamic 3 phase) =
        timeBridgeClockPhase phase) ∧
    (∀ phase : TemporalDynamic,
      dynamicCarrier phase = (timeBridgePresent.entry, timeBridgePresent.exit)) ∧
    timeBridgeArchStandingWave :=
  ⟨past_collapse_clock_phase_value, present_defer_clock_phase_value,
   future_commit_clock_phase_value, past_tick_defers_present,
   present_tick_commits_future, twelve_ticks_close_bridge_phase,
   three_force_steps_preserve_clock_phase, gnosis_clock_projection_preserves_carrier,
   time_bridge_arch_wave_holds⟩

end TimeBridgeGnosisClock
end GnosisMath
