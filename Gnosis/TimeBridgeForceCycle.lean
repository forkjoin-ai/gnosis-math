import Gnosis.TimeBridgePhysicsStandingWaves

/-
  TimeBridgeForceCycle.lean
  =========================

  Closes the current time-bridge loop:

  * future-commit uses Fork / strong-binding,
  * past-collapse uses Race / weak-decay,
  * present-defer uses Fold / electromagnetic coherence,
  * all three readings preserve the same two-port bridge carrier,
  * the arch remains the same keystone standing wave.

  The cycle changes operator phase; it does not change topology.
-/

namespace GnosisMath
namespace TimeBridgeForceCycle

open ForkRaceFoldVentAreForces
open Gnosis.TritonCanonical
open Gnosis.PeruvianArchitect
open GnosisMath.TimeBridgePresentCarrier
open GnosisMath.TimeBridgeTritonDynamics
open GnosisMath.TimeBridgePhysicsStandingWaves

/-- The bridge force phase used by a temporal dynamic. -/
def dynamicForceOperator : TemporalDynamic → MeshOperator
  | .futureCommit => MeshOperator.fork
  | .pastCollapse => MeshOperator.race
  | .presentDefer => MeshOperator.fold

/-- The closed time bridge order: future commit, past collapse, present defer. -/
def timeBridgeForceCycle : List TemporalDynamic :=
  [.futureCommit, .pastCollapse, .presentDefer]

/-- The same cycle read as force operators. -/
def timeBridgeOperatorCycle : List MeshOperator :=
  timeBridgeForceCycle.map dynamicForceOperator

/-- One step of temporal dynamics around the closed bridge cycle. -/
def nextTemporalDynamic : TemporalDynamic → TemporalDynamic
  | .futureCommit => .pastCollapse
  | .pastCollapse => .presentDefer
  | .presentDefer => .futureCommit

/-- Iterate the closed temporal dynamic cycle. -/
def iterateTemporalDynamic : Nat → TemporalDynamic → TemporalDynamic
  | 0, phase => phase
  | n + 1, phase => iterateTemporalDynamic n (nextTemporalDynamic phase)

theorem future_commit_uses_fork :
    dynamicForceOperator TemporalDynamic.futureCommit = MeshOperator.fork :=
  rfl

theorem past_collapse_uses_race :
    dynamicForceOperator TemporalDynamic.pastCollapse = MeshOperator.race :=
  rfl

theorem present_defer_uses_fold :
    dynamicForceOperator TemporalDynamic.presentDefer = MeshOperator.fold :=
  rfl

theorem next_future_commit_is_past_collapse :
    nextTemporalDynamic TemporalDynamic.futureCommit = TemporalDynamic.pastCollapse :=
  rfl

theorem next_past_collapse_is_present_defer :
    nextTemporalDynamic TemporalDynamic.pastCollapse = TemporalDynamic.presentDefer :=
  rfl

theorem next_present_defer_is_future_commit :
    nextTemporalDynamic TemporalDynamic.presentDefer = TemporalDynamic.futureCommit :=
  rfl

/-- The force cycle has exactly the fork/race/fold operator order. -/
theorem time_bridge_operator_cycle_closed :
    timeBridgeOperatorCycle = [MeshOperator.fork, MeshOperator.race, MeshOperator.fold] :=
  rfl

/-- The force cycle has three phases. -/
theorem time_bridge_force_cycle_length :
    timeBridgeForceCycle.length = 3 :=
  rfl

/-- Three temporal steps return any dynamic phase to itself. -/
theorem three_step_temporal_monodromy (phase : TemporalDynamic) :
    iterateTemporalDynamic 3 phase = phase := by
  cases phase <;> rfl

/-- One full cycle preserves the bridge carrier. -/
theorem three_step_monodromy_preserves_carrier (phase : TemporalDynamic) :
    dynamicCarrier (iterateTemporalDynamic 3 phase) = dynamicCarrier phase := by
  rw [three_step_temporal_monodromy]

/-- One full cycle preserves the force-operator phase. -/
theorem three_step_monodromy_preserves_operator (phase : TemporalDynamic) :
    dynamicForceOperator (iterateTemporalDynamic 3 phase) = dynamicForceOperator phase := by
  rw [three_step_temporal_monodromy]

/-- Every phase in the force cycle preserves the same two-port bridge carrier. -/
theorem force_cycle_preserves_carrier
    (phase : TemporalDynamic) (h : phase ∈ timeBridgeForceCycle) :
    dynamicCarrier phase = (timeBridgePresent.entry, timeBridgePresent.exit) := by
  cases phase <;> rfl

/-- The force cycle includes the present-defer standing-wave node. -/
theorem force_cycle_contains_present_defer :
    TemporalDynamic.presentDefer ∈ timeBridgeForceCycle := by
  decide

/-- The force cycle includes future commit and past collapse. -/
theorem force_cycle_contains_boundary_dynamics :
    TemporalDynamic.futureCommit ∈ timeBridgeForceCycle ∧
    TemporalDynamic.pastCollapse ∈ timeBridgeForceCycle := by
  decide

/-- The force cycle's present phase is the Triton middle of the time bridge. -/
theorem force_cycle_present_is_triton_middle :
    verdictTemporalDynamic timeBridgePresent.middle =
      TemporalDynamic.presentDefer :=
  present_defer_is_time_bridge_middle

/-- The force cycle closes over the same keystone standing-wave arch. -/
theorem force_cycle_arch_stays_standing_wave :
    architectural_standing_wave past_boundary future_boundary keystone :=
  time_bridge_arch_is_standing_wave

/--
  Full force-cycle bundle: future/past/present phases map to fork/race/fold,
  the carrier is unchanged for every phase, and the arch remains the same
  keystone standing wave.
-/
theorem time_bridge_force_cycle_bundle :
    timeBridgeOperatorCycle = [MeshOperator.fork, MeshOperator.race, MeshOperator.fold] ∧
    timeBridgeForceCycle.length = 3 ∧
    (∀ phase : TemporalDynamic, iterateTemporalDynamic 3 phase = phase) ∧
    (∀ phase : TemporalDynamic,
      dynamicCarrier (iterateTemporalDynamic 3 phase) = dynamicCarrier phase) ∧
    (∀ phase : TemporalDynamic,
      dynamicForceOperator (iterateTemporalDynamic 3 phase) = dynamicForceOperator phase) ∧
    TemporalDynamic.futureCommit ∈ timeBridgeForceCycle ∧
    TemporalDynamic.pastCollapse ∈ timeBridgeForceCycle ∧
    TemporalDynamic.presentDefer ∈ timeBridgeForceCycle ∧
    (∀ phase : TemporalDynamic, phase ∈ timeBridgeForceCycle →
      dynamicCarrier phase = (timeBridgePresent.entry, timeBridgePresent.exit)) ∧
    verdictTemporalDynamic timeBridgePresent.middle =
      TemporalDynamic.presentDefer ∧
    architectural_standing_wave past_boundary future_boundary keystone :=
  ⟨time_bridge_operator_cycle_closed, time_bridge_force_cycle_length,
   three_step_temporal_monodromy, three_step_monodromy_preserves_carrier,
   three_step_monodromy_preserves_operator,
   force_cycle_contains_boundary_dynamics.1, force_cycle_contains_boundary_dynamics.2,
   force_cycle_contains_present_defer, force_cycle_preserves_carrier,
   force_cycle_present_is_triton_middle, force_cycle_arch_stays_standing_wave⟩

end TimeBridgeForceCycle
end GnosisMath
