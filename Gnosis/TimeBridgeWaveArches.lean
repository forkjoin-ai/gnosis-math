import Gnosis.TimeBridgeForceCycle
import Gnosis.StandingWaveAmplitudeBridge

/-
  TimeBridgeWaveArches.lean
  =========================

  Completes the standing-wave reading of the time bridge arches:

  * the arch is the keystone standing wave between past and future,
  * the present is the Triton/standing-wave node,
  * future and past are the unit antinodes,
  * the force cycle's three-step monodromy preserves the arch carrier.
-/

namespace GnosisMath
namespace TimeBridgeWaveArches

open Gnosis.TritonCanonical
open Gnosis.StandingWaveAmplitudeBridge
open Gnosis.PeruvianArchitect
open GnosisMath.TimeBridgePresentCarrier
open GnosisMath.TimeBridgeTritonDynamics
open GnosisMath.TimeBridgePhysicsStandingWaves
open GnosisMath.TimeBridgeForceCycle

/-- The bridge arch as a standing-wave object: past/future meet at keystone. -/
def timeBridgeArchStandingWave : Prop :=
  architectural_standing_wave past_boundary future_boundary keystone

/-- The present phase is the wave node. -/
theorem present_phase_is_wave_node :
    tritAmplitude timeBridgePresent.middle = 0 := by
  rw [present_middle_is_triton_abstain]
  exact tritAmplitude_abstain

/-- Future commit is a unit antinode. -/
theorem future_commit_is_unit_antinode :
    tritAmplitude Verdict.accept = 1 :=
  tritAmplitude_accept

/-- Past collapse is a unit antinode. -/
theorem past_collapse_is_unit_antinode :
    tritAmplitude Verdict.decline = 1 :=
  tritAmplitude_decline

/-- The two boundary dynamics are exactly the two antinode verdicts. -/
theorem boundary_dynamics_are_antinodes :
    verdictTemporalDynamic Verdict.accept = TemporalDynamic.futureCommit ∧
    tritAmplitude Verdict.accept = 1 ∧
    verdictTemporalDynamic Verdict.decline = TemporalDynamic.pastCollapse ∧
    tritAmplitude Verdict.decline = 1 :=
  ⟨accept_maps_to_future_commit, future_commit_is_unit_antinode,
   decline_maps_to_past_collapse, past_collapse_is_unit_antinode⟩

/-- The standing-wave arch is present at the time bridge. -/
theorem time_bridge_arch_wave_holds :
    timeBridgeArchStandingWave :=
  time_bridge_arch_is_standing_wave

/-- Full force-cycle monodromy preserves the standing-wave arch proposition. -/
theorem force_cycle_monodromy_preserves_arch
    (phase : TemporalDynamic) :
    iterateTemporalDynamic 3 phase = phase ∧ timeBridgeArchStandingWave :=
  ⟨three_step_temporal_monodromy phase, time_bridge_arch_wave_holds⟩

/--
  Wave-arch bundle: the bridge arch is a keystone standing wave, present is the
  node, past/future are antinodes, and full monodromy preserves the arch.
-/
theorem time_bridge_wave_arch_bundle :
    timeBridgeArchStandingWave ∧
    tritAmplitude timeBridgePresent.middle = 0 ∧
    tritAmplitude Verdict.accept = 1 ∧
    tritAmplitude Verdict.decline = 1 ∧
    (∀ phase : TemporalDynamic,
      iterateTemporalDynamic 3 phase = phase ∧ timeBridgeArchStandingWave) :=
  ⟨time_bridge_arch_wave_holds, present_phase_is_wave_node,
   future_commit_is_unit_antinode, past_collapse_is_unit_antinode,
   force_cycle_monodromy_preserves_arch⟩

end TimeBridgeWaveArches
end GnosisMath
