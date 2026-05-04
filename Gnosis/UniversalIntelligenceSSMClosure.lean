import Gnosis.UniversalIntelligenceSSM
import Gnosis.CosmicNoiseConnections

namespace Gnosis
namespace UniversalIntelligenceSSMClosure

open UniversalIntelligenceSSM
open CosmicNoiseConnections
open BuleyTransformerSSMBridge

/-!
# Universal Intelligence SSM Closure Model

This module connects the thermodynamic SSM to the head-disaggregation closure
proved in `Gnosis.CosmicNoiseConnections`.

The model keeps two observer states for the same node:

* the Aeon cut, where 8 attention heads alias into repeated coordinates and
  leave unresolved aggregate residue;
* the resolution-lifted cut, where the same heads separate into distinct
  coordinates and the aggregate residue closes.
-/

/-- Observer-side state for a swarm node with a multi-head attention block. -/
structure ClosureAttentionState where
  node : SwarmNode
  heads : Nat
  coupling : Nat
  observerResolution : Nat
  sourceResolution : Nat
  foldedCoordinate : Nat
  unresolvedResidue : Nat
  headTrace : List Nat

/-- A state's head trace is aliased when projected coordinates collide. -/
def headTraceAliased (state : ClosureAttentionState) : Prop :=
  ¬ state.headTrace.Nodup

/-- A state's head trace is separated when every projected coordinate is unique. -/
def headTraceSeparated (state : ClosureAttentionState) : Prop :=
  state.headTrace.Nodup

/-- Aggregate residue has closed when the observer state carries no leakage. -/
def aggregateResidueClosed (state : ClosureAttentionState) : Prop :=
  state.unresolvedResidue = 0

/-- Runtime optimizer admission derived from the observer-side closure state.

The fields mirror the distributed runtime gates: head pruning, speculative
verification, and standing-wave compression are admitted only after the head
trace separates and aggregate residue closes. Before then, the policy preserves
all heads and requests a resolution lift. -/
structure OptimizerAdmission where
  allowHeadPruning : Bool
  allowSpeculativeDecode : Bool
  allowStandingWaveCompression : Bool
  preserveHeads : Bool
  requiresResolutionLift : Bool

/-- The proof-side predicate for admitting destructive or lossy optimization:
the projected head trace must be separated and aggregate residue must be zero. -/
def optimizerReady (state : ClosureAttentionState) : Prop :=
  headTraceSeparated state ∧ aggregateResidueClosed state

/-- Boolean optimizer policy consumed by runtime mirrors. -/
def optimizerAdmission (state : ClosureAttentionState) : OptimizerAdmission :=
  if state.headTrace.Nodup ∧ state.unresolvedResidue = 0 then
    { allowHeadPruning := true
      allowSpeculativeDecode := true
      allowStandingWaveCompression := true
      preserveHeads := false
      requiresResolutionLift := false }
  else
    { allowHeadPruning := false
      allowSpeculativeDecode := false
      allowStandingWaveCompression := false
      preserveHeads := true
      requiresResolutionLift := true }

/-- Separated, residue-closed observer states admit pruning/speculation/compression. -/
theorem optimizer_ready_admits_runtime_work
    (state : ClosureAttentionState)
    (hReady : optimizerReady state) :
    (optimizerAdmission state).allowHeadPruning = true
    ∧ (optimizerAdmission state).allowSpeculativeDecode = true
    ∧ (optimizerAdmission state).allowStandingWaveCompression = true
    ∧ (optimizerAdmission state).preserveHeads = false
    ∧ (optimizerAdmission state).requiresResolutionLift = false := by
  unfold optimizerReady headTraceSeparated aggregateResidueClosed at hReady
  unfold optimizerAdmission
  simp [hReady]

/-- Aliased head traces fail closed: preserve every head and lift before work. -/
theorem optimizer_alias_requires_resolution_lift
    (state : ClosureAttentionState)
    (hAlias : headTraceAliased state) :
    (optimizerAdmission state).allowHeadPruning = false
    ∧ (optimizerAdmission state).allowSpeculativeDecode = false
    ∧ (optimizerAdmission state).allowStandingWaveCompression = false
    ∧ (optimizerAdmission state).preserveHeads = true
    ∧ (optimizerAdmission state).requiresResolutionLift = true := by
  unfold headTraceAliased at hAlias
  unfold optimizerAdmission
  simp [hAlias]

/-- Non-zero aggregate residue also fails closed, even if the trace separates. -/
theorem optimizer_residue_requires_resolution_lift
    (state : ClosureAttentionState)
    (hResidue : state.unresolvedResidue ≠ 0) :
    (optimizerAdmission state).allowHeadPruning = false
    ∧ (optimizerAdmission state).allowSpeculativeDecode = false
    ∧ (optimizerAdmission state).allowStandingWaveCompression = false
    ∧ (optimizerAdmission state).preserveHeads = true
    ∧ (optimizerAdmission state).requiresResolutionLift = true := by
  unfold optimizerAdmission
  simp [hResidue]

/-- The low-resolution 8-head SSM observer: Aeon bins see the folded shadow. -/
def aeonEightHeadSSMState (node : SwarmNode) : ClosureAttentionState :=
  { node := node
    heads := 8
    coupling := 0
    observerResolution := Gnosis.Circadian.aeon
    sourceResolution := multiHeadPhaseCount 8
    foldedCoordinate := (nHeadAttentionFingerprint 8).coordinate
    unresolvedResidue := (nHeadAttentionFingerprint 8).leakage
    headTrace := nHeadCoordinateTrace 8 Gnosis.Circadian.aeon }

/-- The closure-lifted 8-head SSM observer: full block resolution separates
the heads and removes the bare aggregate residue. -/
def liftedEightHeadSSMState (node : SwarmNode) : ClosureAttentionState :=
  { node := node
    heads := 8
    coupling := 0
    observerResolution := multiHeadPhaseCount 8
    sourceResolution := multiHeadPhaseCount 8
    foldedCoordinate :=
      (fingerprintPhaseAtCeiling
        (multiHeadPhaseCount 8)
        (multiHeadPhaseCount 8)
        (by decide)).coordinate
    unresolvedResidue :=
      (fingerprintPhaseAtCeiling
        (multiHeadPhaseCount 8)
        (multiHeadPhaseCount 8)
        (by decide)).leakage
    headTrace := nHeadCoordinateTrace 8 (multiHeadPhaseCount 8) }

/-- The pink-coupled closure-lifted observer: 8 heads plus Hexon coupling use
the full 30-phase source resolution. -/
def liftedPinkEightHeadSSMState (node : SwarmNode) : ClosureAttentionState :=
  { node := node
    heads := 8
    coupling := multiHeadPhaseCount 2
    observerResolution := multiHeadPhaseCount 8 + multiHeadPhaseCount 2
    sourceResolution := multiHeadPhaseCount 8 + multiHeadPhaseCount 2
    foldedCoordinate :=
      (fingerprintPhaseAtCeiling
        (multiHeadPhaseCount 8 + multiHeadPhaseCount 2)
        (multiHeadPhaseCount 8 + multiHeadPhaseCount 2)
        (by decide)).coordinate
    unresolvedResidue :=
      (fingerprintPhaseAtCeiling
        (multiHeadPhaseCount 8 + multiHeadPhaseCount 2)
        (multiHeadPhaseCount 8 + multiHeadPhaseCount 2)
        (by decide)).leakage
    headTrace :=
      nHeadCoordinateTrace 8 (multiHeadPhaseCount 8 + multiHeadPhaseCount 2) }

/-- The Aeon 8-head observer aliases the trace and keeps the 12-unit residue. -/
theorem aeon_eight_head_ssm_state_aliases
    (node : SwarmNode) :
    headTraceAliased (aeonEightHeadSSMState node)
    ∧ (aeonEightHeadSSMState node).headTrace =
      [3, 6, 9, 0, 3, 6, 9, 0]
    ∧ (aeonEightHeadSSMState node).foldedCoordinate = 0
    ∧ (aeonEightHeadSSMState node).unresolvedResidue = 12 := by
  constructor
  · unfold headTraceAliased aeonEightHeadSSMState
    exact eight_head_aeon_trace_aliases.2
  · constructor
    · unfold aeonEightHeadSSMState
      exact eight_head_aeon_trace_aliases.1
    · constructor
      · unfold aeonEightHeadSSMState
        exact eight_head_attention_shadow_without_coupling.2.1
      · unfold aeonEightHeadSSMState
        exact eight_head_attention_shadow_without_coupling.2.2.1

/-- The 24-resolution 8-head observer separates the trace and closes the bare
aggregate residue. -/
theorem lifted_eight_head_ssm_state_closes
    (node : SwarmNode) :
    headTraceSeparated (liftedEightHeadSSMState node)
    ∧ (liftedEightHeadSSMState node).headTrace =
      [3, 6, 9, 12, 15, 18, 21, 0]
    ∧ aggregateResidueClosed (liftedEightHeadSSMState node) := by
  constructor
  · unfold headTraceSeparated liftedEightHeadSSMState
    exact eight_head_full_resolution_trace_disaggregates.2
  · constructor
    · unfold liftedEightHeadSSMState
      exact eight_head_full_resolution_trace_disaggregates.1
    · unfold aggregateResidueClosed liftedEightHeadSSMState
      exact eight_head_resolution_lift_closes_shadow.2.2.2

/-- The Aeon cut must not prune heads, speculate, or compress standing-wave
routes before lifting resolution. -/
theorem aeon_eight_head_optimizer_requires_lift
    (node : SwarmNode) :
    (optimizerAdmission (aeonEightHeadSSMState node)).allowHeadPruning = false
    ∧ (optimizerAdmission (aeonEightHeadSSMState node)).allowSpeculativeDecode = false
    ∧ (optimizerAdmission (aeonEightHeadSSMState node)).allowStandingWaveCompression = false
    ∧ (optimizerAdmission (aeonEightHeadSSMState node)).preserveHeads = true
    ∧ (optimizerAdmission (aeonEightHeadSSMState node)).requiresResolutionLift = true :=
  optimizer_alias_requires_resolution_lift
    (aeonEightHeadSSMState node)
    (aeon_eight_head_ssm_state_aliases node |>.1)

/-- The 24-resolution lift admits the runtime optimizer surfaces. -/
theorem lifted_eight_head_optimizer_admits_runtime_work
    (node : SwarmNode) :
    (optimizerAdmission (liftedEightHeadSSMState node)).allowHeadPruning = true
    ∧ (optimizerAdmission (liftedEightHeadSSMState node)).allowSpeculativeDecode = true
    ∧ (optimizerAdmission (liftedEightHeadSSMState node)).allowStandingWaveCompression = true
    ∧ (optimizerAdmission (liftedEightHeadSSMState node)).preserveHeads = false
    ∧ (optimizerAdmission (liftedEightHeadSSMState node)).requiresResolutionLift = false :=
  optimizer_ready_admits_runtime_work
    (liftedEightHeadSSMState node)
    ⟨lifted_eight_head_ssm_state_closes node |>.1,
      lifted_eight_head_ssm_state_closes node |>.2.2⟩

/-- The 30-resolution pink-coupled observer separates the 8-head trace and
closes the coupled pink aggregate residue. -/
theorem lifted_pink_eight_head_ssm_state_closes
    (node : SwarmNode) :
    headTraceSeparated (liftedPinkEightHeadSSMState node)
    ∧ aggregateResidueClosed (liftedPinkEightHeadSSMState node)
    ∧ (coupledNHeadAttentionFingerprint 8 (multiHeadPhaseCount 2)).leakage =
      18 := by
  constructor
  · unfold headTraceSeparated liftedPinkEightHeadSSMState
    exact eight_head_hexon_full_resolution_closes_pink_shadow.1
  · constructor
    · unfold aggregateResidueClosed liftedPinkEightHeadSSMState
      exact eight_head_hexon_full_resolution_closes_pink_shadow.2.1
    · exact eight_head_hexon_full_resolution_closes_pink_shadow.2.2

/-- The 30-resolution pink-coupled lift also admits the runtime optimizer
surfaces: the pink residue is resolved into separated coordinates before work
is skipped. -/
theorem lifted_pink_eight_head_optimizer_admits_runtime_work
    (node : SwarmNode) :
    (optimizerAdmission (liftedPinkEightHeadSSMState node)).allowHeadPruning = true
    ∧ (optimizerAdmission (liftedPinkEightHeadSSMState node)).allowSpeculativeDecode = true
    ∧ (optimizerAdmission (liftedPinkEightHeadSSMState node)).allowStandingWaveCompression = true
    ∧ (optimizerAdmission (liftedPinkEightHeadSSMState node)).preserveHeads = false
    ∧ (optimizerAdmission (liftedPinkEightHeadSSMState node)).requiresResolutionLift = false :=
  optimizer_ready_admits_runtime_work
    (liftedPinkEightHeadSSMState node)
    ⟨lifted_pink_eight_head_ssm_state_closes node |>.1,
      lifted_pink_eight_head_ssm_state_closes node |>.2.1⟩

/-- Closure-lifted execution composes with the existing Hebbian SSM rule:
once the folded attention field has been resolved and the route executes, the
node still receives the ordinary thermodynamic reward. -/
theorem closure_lift_preserves_hebbian_reward
    (node other : SwarmNode)
    (hExec : executeAttention node other = true) :
    headTraceSeparated (liftedEightHeadSSMState node)
    ∧ aggregateResidueClosed (liftedEightHeadSSMState node)
    ∧ (hebbianReward node true).energy > node.energy := by
  constructor
  · exact lifted_eight_head_ssm_state_closes node |>.1
  · constructor
    · exact lifted_eight_head_ssm_state_closes node |>.2.2
    · exact swarm_hebbian_convergence node other hExec

end UniversalIntelligenceSSMClosure
end Gnosis
