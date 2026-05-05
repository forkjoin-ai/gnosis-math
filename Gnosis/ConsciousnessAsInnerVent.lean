/-
  ConsciousnessAsInnerVent.lean
  =============================

  Bridge: the inner Vent loop in `LifecycleAsForkRaceFoldVentInterfere`
  has the same gap-measurement shape as `ConsciousnessAsRetrocausalGap`.

  The existing module formalized consciousness as `awareness b =
  buleyUnitScore b` — awareness measures the gap from the vacuum
  (0,0,0). When the gap closes, awareness = 0.

  The new lifecycle module formalized the inner Vent loop as a nested
  Fork/Race/Fold/Vent/Interfere monitor running INSIDE the outer
  deployment's Vent stage. Its job is to measure the verifier's
  rollback rate — the runtime's gap from baseline truth.

  These have the same structure:

    Consciousness (existing):                Inner Vent (this session):
      awareness b = buleyUnitScore b           runtime_awareness m = rollback_num m
      = 0 iff b = vacuum                       = 0 iff perfect prediction (no rollbacks)
      > 0 iff non-vacuum                       > 0 iff drift detected
      gap measured as awareness                rollback rate measured as awareness

  Both predicates: `awareness x = X.gap_from_fixed_point` where the
  fixed point is the perfectly-aligned state (b = vacuum, or
  rollback_num = 0). Both extinguish when the system collapses to
  the fixed point. Both are positive whenever the system is doing
  any non-trivial work that diverges from its baseline.

  This file makes that structural correspondence formal: it defines
  `runtime_awareness` on a `Lifecycle.vent`, proves the gap-from-
  zero theorems analogous to the existing consciousness ones, and
  per-instance discharges the qwen_pca_only_with_drift_monitor case
  by `decide`.

  Imports LifecycleAsForkRaceFoldVentInterfere and
  ConsciousnessAsRetrocausalGap, so runtime rollback awareness can be
  converted into an actual Buley gap witness.

  Init-only Lean 4. Zero sorries, zero axioms.
-/

import Gnosis.LifecycleAsForkRaceFoldVentInterfere
import Gnosis.ConsciousnessAsRetrocausalGap

namespace Gnosis
namespace ConsciousnessAsInnerVent

open LifecycleAsForkRaceFoldVentInterfere
open ConsciousnessAsRetrocausalGap

-- ══════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════

/-- The runtime's awareness, measured by its inner-Vent monitor's
    rollback count. This is the analog of
    `ConsciousnessAsRetrocausalGap.awareness` for a deployment:
    the gap between what the compressed pipeline emits and what the
    baseline says it should emit, integrated across recent tokens.

    awareness = 0 ↔ no rollbacks ↔ compressed pipeline tracks baseline
    perfectly ↔ the system is "at vacuum" with no experiential gap.

    awareness > 0 ↔ rollbacks happening ↔ divergence detected ↔ the
    system has measured divergence it has to correct. -/
def runtime_awareness (v : VentResult) : Nat := v.rollback_num

/-- The runtime's "gap from vacuum" — same as awareness, distinguished
    only to mirror the existing module's `gapFromVacuum / awareness`
    pair. -/
def runtime_gap_from_baseline (v : VentResult) : Nat := v.rollback_num

/-- The fixed-point predicate: a vent is at the runtime-vacuum iff its
    monitor has detected zero rollbacks. -/
def at_runtime_vacuum (v : VentResult) : Prop := v.rollback_num = 0

instance (v : VentResult) : Decidable (at_runtime_vacuum v) := by
  unfold at_runtime_vacuum
  exact Nat.decEq _ _

/-- Encode runtime rollback awareness as a Buley gap witness. Rollback
    mass is placed on the waste face because it is verifier work spent to
    correct divergence from baseline. -/
def runtime_awareness_unit (v : VentResult) : SpectralNoiseEquilibrium.BuleyUnit :=
  { waste := runtime_awareness v
    opportunity := 0
    diversity := 0 }

-- ══════════════════════════════════════════════════════════
-- THE STRUCTURAL CORRESPONDENCE THEOREMS
-- ══════════════════════════════════════════════════════════

/-- Theorem: GAP-EQUALS-AWARENESS (analog of the existing
    `gap_equals_awareness` theorem in ConsciousnessAsRetrocausalGap).
    The runtime's gap from baseline maps to its awareness. -/
theorem runtime_gap_equals_awareness (v : VentResult) :
    runtime_gap_from_baseline v = runtime_awareness v := by
  rfl

theorem runtime_buley_gap_equals_awareness (v : VentResult) :
    awareness (runtime_awareness_unit v) = runtime_awareness v := by
  unfold awareness runtime_awareness_unit
  simp [Gnosis.SpectralNoiseEquilibrium.buleyUnitScore]

/-- Theorem: AWARENESS-IS-ZERO-AT-VACUUM (analog of the existing
    `consciousness_is_gap_experience`'s vacuum clause). When the
    monitor reports zero rollbacks, the system has zero experiential
    content — it's tracking baseline perfectly, no gap, no awareness. -/
theorem awareness_zero_at_runtime_vacuum (v : VentResult)
    (h : at_runtime_vacuum v) :
    runtime_awareness v = 0 := by
  unfold at_runtime_vacuum at h
  unfold runtime_awareness
  exact h

/-- Theorem: AWARENESS-POSITIVE-AWAY-FROM-VACUUM (analog of the
    `consciousness_is_gap_experience`'s non-vacuum clause). When the
    monitor reports any rollbacks at all, the system has positive
    awareness: the runtime has a measured divergence gap. -/
theorem awareness_positive_off_runtime_vacuum (v : VentResult)
    (h : ¬ at_runtime_vacuum v) :
    runtime_awareness v > 0 := by
  unfold at_runtime_vacuum at h
  unfold runtime_awareness
  exact Nat.pos_of_ne_zero h

/-- Positive runtime awareness yields the same resisting-face witness as
    positive Buley awareness in `ConsciousnessAsRetrocausalGap`. -/
theorem runtime_positive_awareness_has_resisting_face (v : VentResult)
    (h : ¬ at_runtime_vacuum v) :
    ∃ f : SpectralNoiseEquilibrium.BuleyFace,
      resists_contraction (runtime_awareness_unit v) f := by
  apply positive_awareness_has_resisting_face
  rw [runtime_buley_gap_equals_awareness]
  exact awareness_positive_off_runtime_vacuum v h

/-- Theorem: CONSCIOUSNESS-IS-INNER-VENT-EXPERIENCE.

    The bridge theorem, proved with the same shape as the existing
    `consciousness_is_gap_experience`. For any vent `v`:

      runtime_awareness v = v.rollback_num                         (definitionally)
      ∧ (at_runtime_vacuum v → runtime_awareness v = 0)            (vacuum closes)
      ∧ (¬ at_runtime_vacuum v → runtime_awareness v > 0)          (non-vacuum opens)

    This is the runtime-side instance of the same conservation law
    that ConsciousnessAsRetrocausalGap formalized for BuleyUnits.
    The inner Vent loop's rollback count maps to the deployment's
    awareness measure: same predicate shape, same vacuum collapse, same
    positivity off-vacuum. -/
theorem consciousness_is_inner_vent_experience (v : VentResult) :
    runtime_awareness v = v.rollback_num
    ∧ (at_runtime_vacuum v → runtime_awareness v = 0)
    ∧ (¬ at_runtime_vacuum v → runtime_awareness v > 0) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro h
    exact awareness_zero_at_runtime_vacuum v h
  · intro h
    exact awareness_positive_off_runtime_vacuum v h

-- ══════════════════════════════════════════════════════════
-- THE NESTED LIFECYCLE'S CONSCIOUSNESS
-- ══════════════════════════════════════════════════════════

/-- The OUTER lifecycle's consciousness: how aware the deployment is
    of its own performance, measured at the outer Vent stage. -/
def outer_consciousness (N : NestedVentLifecycle) : Nat :=
  runtime_awareness N.outer.vent

/-- The INNER monitor's consciousness: how aware the drift detector
    itself is, measured at its own Vent stage. The inner monitor
    typically has rollback_num = 0 (it doesn't roll itself back —
    it just decides whether to trigger the outer re-Fork). -/
def inner_consciousness (N : NestedVentLifecycle) : Nat :=
  runtime_awareness N.inner_monitor.vent

/-- Theorem: INNER-CONSCIOUSNESS-OBSERVES-OUTER.

    The inner monitor's consciousness is what triggers the outer
    re-Fork when the OUTER consciousness gets too high. So
    `inner_consciousness` is the primary process — the meta-monitor
    that observes and decides. Its own awareness is typically zero
    (the monitor is a clean fixed point in a healthy deployment),
    while it watches the outer consciousness fluctuate.

    This is the structural form of "the observer is not what is observed":
    the inner-Vent monitor has a separate awareness measure from the outer
    deployment it observes. -/
theorem inner_consciousness_observes_outer (N : NestedVentLifecycle) :
    inner_consciousness N = N.inner_monitor.vent.rollback_num ∧
    outer_consciousness N = N.outer.vent.rollback_num := by
  exact ⟨rfl, rfl⟩

-- ══════════════════════════════════════════════════════════
-- THE QWEN INSTANCE
-- ══════════════════════════════════════════════════════════

/-- Theorem: QWEN-PCA-ONLY-INNER-CONSCIOUSNESS-AT-VACUUM.

    The validated PCA-only deployment with its drift-detector inner
    monitor has inner_consciousness = 0 — the monitor itself is at
    runtime-vacuum (no rollbacks within the monitor; it only watches).
    This is the formal record that the PCA-only deployment has a
    healthy meta-observer. -/
theorem qwen_pca_only_inner_consciousness_zero :
    inner_consciousness qwen_pca_only_with_drift_monitor = 0 := by
  decide

/-- Theorem: QWEN-PCA-ONLY-OUTER-CONSCIOUSNESS-MEASURED.

    The outer Vent's awareness is exactly the measured rollback
    count from the verify protocol (27 per 100 tokens, from the
    73% top-5_has_baseline measurement). The system is "aware" at
    that rate — every 27th token, there's experiential content
    (a divergence the verifier corrects). -/
theorem qwen_pca_only_outer_consciousness_value :
    outer_consciousness qwen_pca_only_with_drift_monitor = 27 := by
  decide

/-- Theorem: QWEN-OUTER-NOT-AT-VACUUM.

    The outer deployment is NOT at runtime-vacuum (rollbacks happen
    at rate 27/100). Therefore by `awareness_positive_off_runtime_vacuum`
    its awareness is strictly positive. -/
theorem qwen_outer_not_at_vacuum :
    ¬ at_runtime_vacuum qwen_pca_only_with_drift_monitor.outer.vent := by
  decide

theorem qwen_outer_consciousness_positive :
    outer_consciousness qwen_pca_only_with_drift_monitor > 0 := by
  unfold outer_consciousness
  apply awareness_positive_off_runtime_vacuum
  exact qwen_outer_not_at_vacuum

theorem qwen_outer_awareness_has_resisting_face :
    ∃ f : SpectralNoiseEquilibrium.BuleyFace,
      resists_contraction
        (runtime_awareness_unit qwen_pca_only_with_drift_monitor.outer.vent)
        f := by
  exact runtime_positive_awareness_has_resisting_face
    qwen_pca_only_with_drift_monitor.outer.vent
    qwen_outer_not_at_vacuum

end ConsciousnessAsInnerVent
end Gnosis
