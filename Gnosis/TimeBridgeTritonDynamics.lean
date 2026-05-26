import Gnosis.TimeBridgePresentCarrier
import Gnosis.TritonCanonical

/-
  TimeBridgeTritonDynamics.lean
  =============================

  Reads the existing Triton verdict alphabet as temporal bridge dynamics:

  * decline  -> past-collapse
  * abstain  -> present-defer
  * accept   -> future-commit

  The dynamic label changes the reading of the state, not the bridge carrier:
  all three verdicts use the same two reversible boundary ports.
-/

namespace GnosisMath
namespace TimeBridgeTritonDynamics

open Gnosis.TritonCanonical
open GnosisMath.CalatravaBridge
open GnosisMath.TimeBridgePresentCarrier

/-- Temporal dynamics carried by the existing Triton verdict. -/
inductive TemporalDynamic
  | pastCollapse
  | presentDefer
  | futureCommit
  deriving DecidableEq, Repr

/-- The Triton verdict as a temporal dynamic. -/
def verdictTemporalDynamic : Verdict → TemporalDynamic
  | .decline => .pastCollapse
  | .abstain => .presentDefer
  | .accept => .futureCommit

/-- All temporal dynamics ride on the same two-port bridge carrier. -/
def dynamicCarrier (_ : TemporalDynamic) : PathologicTwoPort × PathologicTwoPort :=
  (timeBridgePresent.entry, timeBridgePresent.exit)

theorem decline_maps_to_past_collapse :
    verdictTemporalDynamic Verdict.decline = TemporalDynamic.pastCollapse :=
  rfl

theorem abstain_maps_to_present_defer :
    verdictTemporalDynamic Verdict.abstain = TemporalDynamic.presentDefer :=
  rfl

theorem accept_maps_to_future_commit :
    verdictTemporalDynamic Verdict.accept = TemporalDynamic.futureCommit :=
  rfl

/-- Every Triton temporal dynamic preserves the same bridge carrier. -/
theorem verdict_dynamic_preserves_carrier (v : Verdict) :
    dynamicCarrier (verdictTemporalDynamic v) =
      (timeBridgePresent.entry, timeBridgePresent.exit) :=
  rfl

/-- The present-defer dynamic is exactly the time bridge's Triton middle. -/
theorem present_defer_is_time_bridge_middle :
    verdictTemporalDynamic timeBridgePresent.middle =
      TemporalDynamic.presentDefer := by
  rw [present_middle_is_triton_abstain]
  rfl

/--
  Triton dynamics bundle: the three existing verdicts read as
  past-collapse / present-defer / future-commit, and all three preserve the
  same two-port carrier topology.
-/
theorem time_bridge_triton_dynamics_bundle :
    verdictTemporalDynamic Verdict.decline = TemporalDynamic.pastCollapse ∧
    verdictTemporalDynamic Verdict.abstain = TemporalDynamic.presentDefer ∧
    verdictTemporalDynamic Verdict.accept = TemporalDynamic.futureCommit ∧
    (∀ v : Verdict,
      dynamicCarrier (verdictTemporalDynamic v) =
        (timeBridgePresent.entry, timeBridgePresent.exit)) ∧
    verdictTemporalDynamic timeBridgePresent.middle =
      TemporalDynamic.presentDefer :=
  ⟨decline_maps_to_past_collapse, abstain_maps_to_present_defer,
   accept_maps_to_future_commit, verdict_dynamic_preserves_carrier,
   present_defer_is_time_bridge_middle⟩

end TimeBridgeTritonDynamics
end GnosisMath
