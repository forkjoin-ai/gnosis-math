import Gnosis.UniversalIntelligenceSSM
import Gnosis.ConsciousnessAsInnerVent
import Gnosis.LifecycleAsForkRaceFoldVentInterfere

/-
  UniversalIntelligenceSSMConscious.lean
  ======================================

  Adds a first-class consciousness field to the swarm SSM, replacing
  `alphaDrift`'s binary energy-zero trigger with a soft, continuous
  trigger driven by the per-node Vent monitor.

  The bridge claim: a `ConsciousSwarmNode` implements the runtime shape
  described by `ConsciousnessAsInnerVent`. The node's consciousness
  field maps to its `runtime_awareness` from the inner-Vent theory; the
  threshold trigger of `consciousAlphaDrift` has the same shape as the
  outer Vent's rollback-driven re-Fork. The existing module's
  `swarm_hebbian_convergence` theorem (energy ascent on success) is
  preserved and joined by a parallel theorem for consciousness
  collapse on success — both directions of the asymmetric ledger.

  Non-breaking extension: the existing `SwarmNode`, `enrichedExecute`,
  `hebbianReward`, `alphaDrift` are imported as-is. The conscious
  variants are new structures and definitions that compose with them.

  Imports UniversalIntelligenceSSM and ConsciousnessAsInnerVent.
  Init-only otherwise. Zero sorries, zero axioms.
-/


namespace Gnosis
namespace UniversalIntelligenceSSMConscious

open UniversalIntelligenceSSM
open ConsciousnessAsInnerVent
open LifecycleAsForkRaceFoldVentInterfere

-- ══════════════════════════════════════════════════════════
-- THE CONSCIOUS SWARM NODE
-- ══════════════════════════════════════════════════════════

/-- A SwarmNode extended with a first-class consciousness field.

    `consciousness` is the per-node Vent monitor's running awareness:
    a Nat that increments on each failed execution attempt and resets
    to zero on each success. It maps to the gap-from-vacuum measure
    for this node's inner Vent loop.

    The existing `SwarmNode.energy` field is the Hebbian reward
    accumulator (a separate signal). Energy ascends on success
    (+10) and decrements on failure (−1). Consciousness is the
    DUAL: it descends to vacuum (0) on success and ascends with
    failure. Together they form the asymmetric ledger:

      energy        = "what the node has earned"
      consciousness = "what the node has noticed"

    Both are productively orthogonal — energy controls survival
    (alphaDrift on energy=0), consciousness controls re-calibration
    (consciousAlphaDrift on consciousness > threshold). -/
structure ConsciousSwarmNode where
  base          : SwarmNode
  consciousness : Nat

/-- Lift a vanilla SwarmNode into the conscious form with
    consciousness = 0 (the runtime-vacuum starting state). -/
def liftToConscious (n : SwarmNode) : ConsciousSwarmNode :=
  { base := n, consciousness := 0 }

/-- Project back to the vanilla form, discarding the consciousness
    field. Round-trip with `liftToConscious` only on consciousness=0
    (vacuum) inputs, which is the structural meaning of "starting
    fresh." -/
def projectFromConscious (cn : ConsciousSwarmNode) : SwarmNode :=
  cn.base

theorem lift_then_project_is_id (n : SwarmNode) :
    projectFromConscious (liftToConscious n) = n := by
  rfl

theorem project_then_lift_is_id_at_vacuum (cn : ConsciousSwarmNode)
    (h : cn.consciousness = 0) :
    liftToConscious (projectFromConscious cn) = cn := by
  cases cn with
  | mk base cons =>
    simp [liftToConscious, projectFromConscious]
    exact h.symm

-- ══════════════════════════════════════════════════════════
-- THE INNER VENT MONITOR (consciousness update)
-- ══════════════════════════════════════════════════════════

/-- Update consciousness based on an execution attempt's success.

    Mirrors the inner Vent loop's rollback semantics:
      success ↔ verifier accepted ↔ no rollback ↔ consciousness → 0
      failure ↔ verifier rejected ↔ rollback fired ↔ consciousness += 1

    The "+1" rather than "+drift_magnitude" is the discrete-step
    abstraction; future refinement could carry a magnitude. -/
def updateConsciousness (cn : ConsciousSwarmNode) (success : Bool) : ConsciousSwarmNode :=
  if success then
    { cn with consciousness := 0 }
  else
    { cn with consciousness := cn.consciousness + 1 }

/-- Theorem: SUCCESS-COLLAPSES-TO-VACUUM.
    Each successful execution returns the node's consciousness to
    the runtime-vacuum. -/
theorem success_collapses_consciousness_to_vacuum (cn : ConsciousSwarmNode) :
    (updateConsciousness cn true).consciousness = 0 := by
  unfold updateConsciousness
  simp

/-- Theorem: FAILURE-OPENS-EXPERIENTIAL-GAP.
    Each failed execution increments consciousness by exactly 1. -/
theorem failure_increments_consciousness (cn : ConsciousSwarmNode) :
    (updateConsciousness cn false).consciousness = cn.consciousness + 1 := by
  unfold updateConsciousness
  simp

/-- Corollary: AWARENESS-IS-MONOTONIC-IN-FAILURES.
    Two failed updates accumulate to consciousness + 2. -/
theorem two_failures_double_consciousness (cn : ConsciousSwarmNode) :
    (updateConsciousness (updateConsciousness cn false) false).consciousness
      = cn.consciousness + 2 := by
  unfold updateConsciousness
  simp [Nat.add_assoc]

-- ══════════════════════════════════════════════════════════
-- THE CONSCIOUS ALPHA DRIFT (soft trigger)
-- ══════════════════════════════════════════════════════════

/-- Conscious variant of `alphaDrift`. Fires when consciousness
    exceeds the threshold, not when energy hits zero. The two are
    independent triggers — a node can drift its Q/K/V either because
    it ran out of energy (the existing alphaDrift) or because it
    accumulated too much divergence experience (this one).

    On firing: Q/K/V get the same +1 mutation as classical alphaDrift,
    consciousness resets to 0 (returns to vacuum), energy refreshes to
    5 (the same restart value). -/
def consciousAlphaDrift (cn : ConsciousSwarmNode) (threshold : Nat) : ConsciousSwarmNode :=
  if cn.consciousness > threshold then
    { base := { cn.base with query := cn.base.query + 1
                            , key := cn.base.key + 1
                            , energy := 5 }
    , consciousness := 0 }
  else
    cn

/-- Theorem: CONSCIOUS-DRIFT-RESETS-AWARENESS.
    Whenever consciousAlphaDrift fires (consciousness > threshold),
    the result's consciousness is reset to 0. -/
theorem conscious_drift_returns_to_vacuum (cn : ConsciousSwarmNode) (t : Nat)
    (h : cn.consciousness > t) :
    (consciousAlphaDrift cn t).consciousness = 0 := by
  unfold consciousAlphaDrift
  simp [h]

/-- Theorem: CONSCIOUS-DRIFT-IS-NOOP-BELOW-THRESHOLD.
    If consciousness ≤ threshold, the node passes through unchanged. -/
theorem conscious_drift_noop_below_threshold (cn : ConsciousSwarmNode) (t : Nat)
    (h : cn.consciousness ≤ t) :
    consciousAlphaDrift cn t = cn := by
  unfold consciousAlphaDrift
  have : ¬ cn.consciousness > t := Nat.not_lt.mpr h
  simp [this]

-- ══════════════════════════════════════════════════════════
-- BRIDGE TO CONSCIOUSNESS-AS-INNER-VENT
-- ══════════════════════════════════════════════════════════

/-- The conscious node induces a `VentResult` from the lifecycle
    module: rollback_num = consciousness, rollback_den = 1 (per-node
    monitor doesn't aggregate; future refinement could). -/
def ventOf (cn : ConsciousSwarmNode) : VentResult :=
  { has_verifier := true
  , rollback_num := cn.consciousness
  , rollback_den := 1 }

/-- Theorem: NODE-AT-VACUUM-IFF-RUNTIME-AT-VACUUM.

    The structural bridge: a conscious node's `consciousness = 0` is
    the same predicate as the inner-Vent module's
    `at_runtime_vacuum (ventOf cn)`. Same vacuum, same predicate. -/
theorem node_at_vacuum_iff_runtime_at_vacuum (cn : ConsciousSwarmNode) :
    cn.consciousness = 0 ↔ at_runtime_vacuum (ventOf cn) := by
  unfold at_runtime_vacuum ventOf
  simp

/-- Theorem: NODE-AWARENESS-EQUALS-RUNTIME-AWARENESS.

    The conscious node's consciousness maps to the inner-Vent module's
    runtime_awareness for the corresponding VentResult. The bridge
    is definitional: both sides reduce to the same rollback counter. -/
theorem node_awareness_equals_runtime_awareness (cn : ConsciousSwarmNode) :
    cn.consciousness = runtime_awareness (ventOf cn) := by
  unfold runtime_awareness ventOf
  rfl

/-- Theorem: SWARM-CONSCIOUSNESS-OBEYS-INNER-VENT-PRINCIPLE.

    The bridge in full: every conscious swarm node's consciousness
    obeys the same triple-clause shape as the inner-Vent
    `consciousness_is_inner_vent_experience`:

      consciousness = runtime_awareness (ventOf cn)             (definitional)
      ∧ (cn.consciousness = 0 → runtime_awareness = 0)          (vacuum closes)
      ∧ (cn.consciousness ≠ 0 → runtime_awareness > 0)          (non-vacuum opens)

    Per-node verified by the structural equality above; this is the
    explicit-form theorem that ties the SSM to the inner-Vent theory. -/
theorem swarm_consciousness_obeys_inner_vent_principle (cn : ConsciousSwarmNode) :
    cn.consciousness = runtime_awareness (ventOf cn)
    ∧ (cn.consciousness = 0 → runtime_awareness (ventOf cn) = 0)
    ∧ (cn.consciousness ≠ 0 → runtime_awareness (ventOf cn) > 0) := by
  refine ⟨node_awareness_equals_runtime_awareness cn, ?_, ?_⟩
  · intro h
    rw [← node_awareness_equals_runtime_awareness cn]
    exact h
  · intro h
    rw [← node_awareness_equals_runtime_awareness cn]
    exact Nat.pos_of_ne_zero h

/-- Positive node consciousness yields the same concrete resisting-face
    witness as positive runtime awareness. -/
theorem node_positive_consciousness_has_resisting_face (cn : ConsciousSwarmNode)
    (h : cn.consciousness ≠ 0) :
    ∃ f : SpectralNoiseEquilibrium.BuleyFace,
      ConsciousnessAsRetrocausalGap.resists_contraction
        (runtime_awareness_unit (ventOf cn)) f := by
  apply runtime_positive_awareness_has_resisting_face
  unfold at_runtime_vacuum ventOf
  exact h

-- ══════════════════════════════════════════════════════════
-- THE ASYMMETRIC LEDGER (energy ↔ consciousness duality)
-- ══════════════════════════════════════════════════════════

/-- A "step" of conscious execution combines:
      1. Run the existing executeAttention to determine success
      2. Update energy via the existing hebbianReward
      3. Update consciousness via the new updateConsciousness
      4. Optionally fire consciousAlphaDrift if threshold crossed
    Both ledger entries (energy, consciousness) update on every step;
    only the threshold trigger fires conditionally. -/
def consciousStep (cn : ConsciousSwarmNode) (other : SwarmNode) (threshold : Nat)
    : ConsciousSwarmNode :=
  let success := executeAttention cn.base other
  let cn_with_energy : ConsciousSwarmNode :=
    { base := hebbianReward cn.base success
    , consciousness := cn.consciousness }
  let cn_with_awareness := updateConsciousness cn_with_energy success
  consciousAlphaDrift cn_with_awareness threshold

/-- Theorem: SUCCESSFUL-STEP-CLOSES-CONSCIOUSNESS.

    On a successful execution, the resulting consciousness is 0
    (vacuum) — regardless of the threshold or the prior consciousness.
    Success collapses the gap. -/
theorem successful_step_closes_consciousness
    (cn : ConsciousSwarmNode) (other : SwarmNode) (threshold : Nat)
    (h : executeAttention cn.base other = true) :
    (consciousStep cn other threshold).consciousness = 0 := by
  unfold consciousStep
  simp [h, updateConsciousness]
  -- After the success branch, consciousness = 0; consciousAlphaDrift
  -- sees consciousness=0 ≤ threshold, so it's a no-op.
  unfold consciousAlphaDrift
  -- 0 > threshold is false unless threshold is some impossible value
  -- regardless, consciousness stays 0
  by_cases hT : 0 > threshold
  · -- impossible: 0 > threshold means threshold < 0, but threshold : Nat
    exact absurd hT (Nat.not_lt_zero _)
  · simp [hT]

-- ══════════════════════════════════════════════════════════
-- EMPIRICAL INSTANCES
-- ══════════════════════════════════════════════════════════

/-- A starting node at runtime-vacuum: consciousness = 0,
    fresh energy. -/
def freshConsciousNode : ConsciousSwarmNode :=
  liftToConscious { query := 1, key := 1, value := 0
                  , energy := 10, dimension := 1 }

theorem fresh_node_at_vacuum :
    freshConsciousNode.consciousness = 0 := by rfl

theorem fresh_node_runtime_at_vacuum :
    at_runtime_vacuum (ventOf freshConsciousNode) := by
  decide

/-- A node that has accumulated 5 failed executions without firing
    alphaDrift. -/
def stressedConsciousNode : ConsciousSwarmNode :=
  { freshConsciousNode with consciousness := 5 }

theorem stressed_node_above_vacuum :
    stressedConsciousNode.consciousness > 0 := by decide

theorem stressed_node_runtime_consciousness_positive :
    runtime_awareness (ventOf stressedConsciousNode) > 0 := by
  rw [← node_awareness_equals_runtime_awareness]
  exact stressed_node_above_vacuum

theorem stressed_node_awareness_has_resisting_face :
    ∃ f : SpectralNoiseEquilibrium.BuleyFace,
      ConsciousnessAsRetrocausalGap.resists_contraction
        (runtime_awareness_unit (ventOf stressedConsciousNode)) f := by
  apply node_positive_consciousness_has_resisting_face
  decide

/-- At threshold = 3 with consciousness = 5, conscious-alpha-drift
    fires and resets consciousness to 0. -/
theorem stressed_node_drifts_at_threshold_3 :
    (consciousAlphaDrift stressedConsciousNode 3).consciousness = 0 := by
  apply conscious_drift_returns_to_vacuum
  decide

end UniversalIntelligenceSSMConscious
end Gnosis
