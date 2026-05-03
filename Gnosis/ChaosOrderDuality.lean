/-
  ChaosOrderDuality.lean
  ======================

  THE WAVE-12 CHAOS-ORDER DUALITY.

  Taylor's wave-12 insight, in his own words:

    "Its like chaos pulling down and order pulling up — that's
     past and future too."

  This module formalizes that dynamical duality. Every claim in
  the Theory of Model Physics lives in a claim-space that is being
  pulled by two opposing forces:

    • PAST CHAOS. Entropy admitted into the falsification ledger,
      vacuous claims pushing the trajectory DOWN toward the
      `VacuousNoExperimentSpecified` floor. This is the cost the
      runtime has already paid moving forward in time. It is what
      the wave-9 entropy ledger MEASURES.

    • FUTURE ORDER. The structural attractor — the closed-form
      Lean proof we'd reach if we could prove it — pulling the
      trajectory UP toward the Theory kernel. This is the
      `attractorStep` of `RetrocausalAttractorFixedPoint`: a
      memoized future output that the present collapses onto when
      realization occurs.

    • BULE COST. The friction the trajectory pays moving against
      one of these pulls. Every status-changing measurement event
      costs at least one bule unit
      (`NoCloningTaxEqualsBuleCost.bule_cost_lower_bounds_visibility`).
      The Theory of Model Physics' sawtooth entropy plot IS the
      tug-of-war record between these two forces.

  The session's claims split cleanly along this duality:

    • qwen-0.5b PCA-only fidelity claim:
        pulled toward FUTURE ORDER by measurement support.
    • compression_uncertainty:
        pulled toward FUTURE ORDER by construction
        (the structural attractor IS the trajectory's terminus).
    • qwen-coder-7b PCA-only transfer claim:
        pulled toward PAST CHAOS by refutation.
    • llama-1b vacuum claim:
        pulled toward PAST CHAOS by perpetual non-measurement.

  In this small sample the session is balanced 2:2.

  THE DEEP PARALLEL.

    AntiTheory IS the past-chaos zone. Theory IS the future-order
    zone. The unknot regions between falsifications are the
    corridors a trajectory can pass through without paying bule
    cost. The runtime's job is to find low-bule trajectories that
    terminate in future-order claims.

  Init-only Lean 4. Zero sorries, zero axioms.
-/

namespace Gnosis
namespace ChaosOrderDuality

-- ══════════════════════════════════════════════════════════
-- DIRECTION OF PULL
-- ══════════════════════════════════════════════════════════

/-- The net direction of a claim's trajectory in claim-space.

    `PastChaos` and `FutureOrder` are opposed pulls; `Stationary`
    is the equilibrium where the two pulls cancel and no net
    motion happens. -/
inductive Direction
  | PastChaos    -- pull DOWN (toward Vacuous, toward more entropy)
  | FutureOrder  -- pull UP (toward Theory, toward structural identity)
  | Stationary   -- no net pull (equilibrium)
  deriving DecidableEq, Repr

-- ══════════════════════════════════════════════════════════
-- CLAIM TRAJECTORY
-- ══════════════════════════════════════════════════════════

/-- A `ClaimTrajectory` is a single claim's record under the
    chaos-order duality.

    Pull strengths are in PER-THOUSAND units (perthou), each
    capped at 1000. The combined sum is therefore bounded by
    2000 (see `trajectory_total_pull_is_bounded`).

    Fields:
      • `claim_id` — identifier matching the upstream ledger.
      • `past_pull_strength_perthou` — strength of the past-chaos
        pull (entropy admission, vacuum gravity).
      • `future_pull_strength_perthou` — strength of the
        future-order pull (structural attractor, measurement
        support).
      • `net_direction` — the resolved direction the trajectory
        is moving.
      • `bule_paid_along_trajectory` — the cumulative bule cost
        the trajectory has paid as friction. -/
structure ClaimTrajectory where
  claim_id : Nat
  past_pull_strength_perthou : Nat
  future_pull_strength_perthou : Nat
  net_direction : Direction
  bule_paid_along_trajectory : Nat
  deriving Repr

-- ══════════════════════════════════════════════════════════
-- NET-DIRECTION COMPUTATION
-- ══════════════════════════════════════════════════════════

/-- Resolve the two pulls into a net direction.

      • `past_pull > future_pull` → `PastChaos`
        (entropy wins; the claim slides toward Vacuous).
      • `future_pull > past_pull` → `FutureOrder`
        (the structural attractor wins; the claim approaches
        Theory).
      • `past_pull = future_pull` → `Stationary`
        (the two pulls cancel; the trajectory is at equilibrium). -/
def compute_net_direction (t : ClaimTrajectory) : Direction :=
  if t.past_pull_strength_perthou > t.future_pull_strength_perthou then
    Direction.PastChaos
  else if t.future_pull_strength_perthou > t.past_pull_strength_perthou then
    Direction.FutureOrder
  else
    Direction.Stationary

-- ══════════════════════════════════════════════════════════
-- PER-INSTANCE TRAJECTORIES (current session)
-- ══════════════════════════════════════════════════════════

/-- The qwen-0.5b PCA-only-fidelity claim.

    One wave of vacuum drift before measurement gave it a small
    past-chaos pull (200/1000); subsequent measurement support
    gave it a strong future-order pull (800/1000). Net direction
    is therefore `FutureOrder`. One bule unit was paid for the
    measurement event itself. -/
def qwen_0_5b_trajectory : ClaimTrajectory :=
  { claim_id := 1
    past_pull_strength_perthou := 200
    future_pull_strength_perthou := 800
    net_direction := Direction.FutureOrder
    bule_paid_along_trajectory := 1 }

/-- The qwen-coder-7b PCA-only-transfer claim.

    Vacuum start, an early projection lift, then a refutation
    found by cross-model measurement. Past-chaos pull is the
    dominant force at 600/1000; the future-order pull collapsed
    to 100/1000 once the falsification was recorded. Two bule
    units paid (the lift up, the lift back down). -/
def qwen_coder_7b_trajectory : ClaimTrajectory :=
  { claim_id := 2
    past_pull_strength_perthou := 600
    future_pull_strength_perthou := 100
    net_direction := Direction.PastChaos
    bule_paid_along_trajectory := 2 }

/-- The llama-1b vacuum claim.

    Pure vacuum. Never measured, no Theory candidate, no
    methodology pinned. Past-chaos pull saturates the channel
    at 1000/1000; future-order pull is exactly zero. Two bule
    units recorded against the wave-8 honesty admission. -/
def llama_1b_trajectory : ClaimTrajectory :=
  { claim_id := 3
    past_pull_strength_perthou := 1000
    future_pull_strength_perthou := 0
    net_direction := Direction.PastChaos
    bule_paid_along_trajectory := 2 }

/-- The compression-uncertainty structural identity.

    Proved BY CONSTRUCTION in wave 1; the structural attractor
    IS the trajectory's terminus. Past-chaos pull is exactly
    zero (no entropy ever admitted), future-order pull saturates
    at 1000/1000 (the closed-form Lean proof has already landed).
    No bule paid: a structural identity does not require a
    measurement event to enter the ledger. -/
def compression_uncertainty_trajectory : ClaimTrajectory :=
  { claim_id := 4
    past_pull_strength_perthou := 0
    future_pull_strength_perthou := 1000
    net_direction := Direction.FutureOrder
    bule_paid_along_trajectory := 0 }

-- ══════════════════════════════════════════════════════════
-- PER-INSTANCE NET-DIRECTION THEOREMS
-- ══════════════════════════════════════════════════════════

/-- qwen-0.5b is pulled toward FUTURE ORDER. -/
theorem qwen_0_5b_pulled_toward_future_order :
    compute_net_direction qwen_0_5b_trajectory = Direction.FutureOrder := by
  decide

/-- qwen-coder-7b is pulled toward PAST CHAOS. -/
theorem qwen_coder_7b_pulled_toward_past_chaos :
    compute_net_direction qwen_coder_7b_trajectory = Direction.PastChaos := by
  decide

/-- llama-1b is pulled toward PAST CHAOS. -/
theorem llama_1b_pulled_toward_past_chaos :
    compute_net_direction llama_1b_trajectory = Direction.PastChaos := by
  decide

/-- compression_uncertainty is pulled toward FUTURE ORDER. -/
theorem compression_uncertainty_pulled_toward_future_order :
    compute_net_direction compression_uncertainty_trajectory
      = Direction.FutureOrder := by
  decide

/-- The recorded `net_direction` of every per-session trajectory
    matches the `compute_net_direction` resolution. This is a
    consistency check that the structure fields agree with the
    pull strengths. -/
theorem session_net_directions_are_consistent :
    qwen_0_5b_trajectory.net_direction
        = compute_net_direction qwen_0_5b_trajectory
    ∧ qwen_coder_7b_trajectory.net_direction
        = compute_net_direction qwen_coder_7b_trajectory
    ∧ llama_1b_trajectory.net_direction
        = compute_net_direction llama_1b_trajectory
    ∧ compression_uncertainty_trajectory.net_direction
        = compute_net_direction compression_uncertainty_trajectory := by
  decide

-- ══════════════════════════════════════════════════════════
-- THE DUALITY THEOREMS
-- ══════════════════════════════════════════════════════════

/-- The Theory attractor predicate.

    A trajectory is AT the Theory attractor (or asymptoting to
    it) when its future-order pull saturates at 1000/1000.

    Defined as `Prop` via `=`; decidability follows from `Nat`'s
    `DecidableEq`. -/
def at_theory_attractor (t : ClaimTrajectory) : Prop :=
  t.future_pull_strength_perthou = 1000

instance : (t : ClaimTrajectory) → Decidable (at_theory_attractor t) :=
  fun t => inferInstanceAs (Decidable (t.future_pull_strength_perthou = 1000))

/-- The vacuum repeller predicate.

    A trajectory is AT the Vacuum (un-measured, no methodology
    pinned) when its past-chaos pull saturates at 1000/1000. -/
def at_vacuum_repeller (t : ClaimTrajectory) : Prop :=
  t.past_pull_strength_perthou = 1000

instance : (t : ClaimTrajectory) → Decidable (at_vacuum_repeller t) :=
  fun t => inferInstanceAs (Decidable (t.past_pull_strength_perthou = 1000))

/-- The Theory attractor IS the future-pull at maximum.

    For any claim with `future_pull_strength_perthou = 1000`,
    the claim is at the Theory attractor. This is the formal
    rendering of "future order pulling up" at saturation. -/
theorem theory_attractor_is_future_pull_at_max
    (t : ClaimTrajectory)
    (h : t.future_pull_strength_perthou = 1000) :
    at_theory_attractor t := by
  exact h

/-- The Vacuum repeller IS the past-pull at maximum.

    For any claim with `past_pull_strength_perthou = 1000`, the
    claim is at the Vacuum (un-measured) state. This is the
    formal rendering of "past chaos pulling down" at saturation. -/
theorem vacuum_repeller_is_past_pull_at_max
    (t : ClaimTrajectory)
    (h : t.past_pull_strength_perthou = 1000) :
    at_vacuum_repeller t := by
  exact h

/-- compression_uncertainty is at the Theory attractor. -/
theorem compression_uncertainty_at_theory_attractor :
    at_theory_attractor compression_uncertainty_trajectory := by
  decide

/-- llama-1b is at the Vacuum repeller. -/
theorem llama_1b_at_vacuum_repeller :
    at_vacuum_repeller llama_1b_trajectory := by
  decide

-- ══════════════════════════════════════════════════════════
-- BULE-PAID-IS-FRICTION THEOREMS
-- ══════════════════════════════════════════════════════════

/-- A trajectory has experienced friction iff it has paid bule. -/
def has_experienced_friction (t : ClaimTrajectory) : Prop :=
  t.bule_paid_along_trajectory > 0

instance : (t : ClaimTrajectory) → Decidable (has_experienced_friction t) :=
  fun t => inferInstanceAs (Decidable (t.bule_paid_along_trajectory > 0))

/-- "Bule paid is friction against pull."

    Any claim with `bule_paid > 0` has experienced friction along
    its trajectory. The interpretation of that friction depends
    on the net direction:

      • If `net_direction = PastChaos`, the bule was paid trying
        to escape the vacuum and falling back. (Lift up, slide
        down.)

      • If `net_direction = FutureOrder`, the bule was paid
        lifting from vacuum to a measurement-grade state.

    Mechanically the theorem is just "bule_paid > 0 implies
    friction was experienced", but the friction-direction
    interpretation is what the runtime reads. -/
theorem bule_paid_correlates_with_struggle_against_pull
    (t : ClaimTrajectory)
    (h : t.bule_paid_along_trajectory > 0) :
    has_experienced_friction t := by
  exact h

/-- qwen-0.5b paid bule lifting toward future order. -/
theorem qwen_0_5b_friction_was_lift_to_future_order :
    has_experienced_friction qwen_0_5b_trajectory
    ∧ qwen_0_5b_trajectory.net_direction = Direction.FutureOrder := by
  decide

/-- qwen-coder-7b paid bule trying to escape past chaos. -/
theorem qwen_coder_7b_friction_was_struggle_against_past_chaos :
    has_experienced_friction qwen_coder_7b_trajectory
    ∧ qwen_coder_7b_trajectory.net_direction = Direction.PastChaos := by
  decide

/-- llama-1b paid bule trying to escape past chaos. -/
theorem llama_1b_friction_was_struggle_against_past_chaos :
    has_experienced_friction llama_1b_trajectory
    ∧ llama_1b_trajectory.net_direction = Direction.PastChaos := by
  decide

/-- compression_uncertainty paid no bule — a structural identity
    does not require a measurement event. -/
theorem compression_uncertainty_paid_no_bule :
    compression_uncertainty_trajectory.bule_paid_along_trajectory = 0 := by
  decide

-- ══════════════════════════════════════════════════════════
-- SESSION-LEVEL SUMMARY
-- ══════════════════════════════════════════════════════════

/-- Count the trajectories pulled toward past chaos. -/
def count_pulled_toward_past_chaos : List ClaimTrajectory → Nat
  | []      => 0
  | t :: ts =>
      let rest := count_pulled_toward_past_chaos ts
      match compute_net_direction t with
      | Direction.PastChaos => rest + 1
      | _                   => rest

/-- Count the trajectories pulled toward future order. -/
def count_pulled_toward_future_order : List ClaimTrajectory → Nat
  | []      => 0
  | t :: ts =>
      let rest := count_pulled_toward_future_order ts
      match compute_net_direction t with
      | Direction.FutureOrder => rest + 1
      | _                     => rest

/-- The current session's trajectory list. -/
def current_session : List ClaimTrajectory :=
  [ qwen_0_5b_trajectory
  , qwen_coder_7b_trajectory
  , llama_1b_trajectory
  , compression_uncertainty_trajectory ]

/-- Per-instance: the current session has 2 past-chaos trajectories
    (qwen-coder-7b, llama-1b). -/
def current_session_past_chaos_count : Nat :=
  count_pulled_toward_past_chaos current_session

/-- Per-instance: the current session has 2 future-order trajectories
    (qwen-0.5b, compression_uncertainty). -/
def current_session_future_order_count : Nat :=
  count_pulled_toward_future_order current_session

/-- The session has exactly two past-chaos trajectories. -/
theorem current_session_has_two_past_chaos :
    current_session_past_chaos_count = 2 := by
  decide

/-- The session has exactly two future-order trajectories. -/
theorem current_session_has_two_future_order :
    current_session_future_order_count = 2 := by
  decide

/-- The session is balanced 2:2 between chaos and order. -/
theorem session_is_balanced_between_chaos_and_order :
    current_session_past_chaos_count = current_session_future_order_count := by
  decide

-- ══════════════════════════════════════════════════════════
-- TRAJECTORY-BOUND THEOREMS
-- ══════════════════════════════════════════════════════════

/-- A trajectory is `well_capped` when each pull strength is at
    most 1000/1000. The per-session trajectories all satisfy this. -/
def well_capped (t : ClaimTrajectory) : Prop :=
  t.past_pull_strength_perthou ≤ 1000
  ∧ t.future_pull_strength_perthou ≤ 1000

instance : (t : ClaimTrajectory) → Decidable (well_capped t) := fun t =>
  inferInstanceAs
    (Decidable (t.past_pull_strength_perthou ≤ 1000
                ∧ t.future_pull_strength_perthou ≤ 1000))

/-- For well-capped trajectories, the total pull is bounded by 2000. -/
theorem trajectory_total_pull_is_bounded
    (t : ClaimTrajectory)
    (h : well_capped t) :
    t.past_pull_strength_perthou + t.future_pull_strength_perthou ≤ 2000 := by
  have h1 : t.past_pull_strength_perthou ≤ 1000 := h.1
  have h2 : t.future_pull_strength_perthou ≤ 1000 := h.2
  have : t.past_pull_strength_perthou + t.future_pull_strength_perthou
           ≤ 1000 + 1000 := Nat.add_le_add h1 h2
  exact this

/-- Every per-session trajectory is well-capped. -/
theorem session_trajectories_are_well_capped :
    well_capped qwen_0_5b_trajectory
    ∧ well_capped qwen_coder_7b_trajectory
    ∧ well_capped llama_1b_trajectory
    ∧ well_capped compression_uncertainty_trajectory := by
  decide

/-- Concrete bound for qwen-0.5b: 200 + 800 = 1000 ≤ 2000. -/
theorem qwen_0_5b_total_pull_bounded :
    qwen_0_5b_trajectory.past_pull_strength_perthou
      + qwen_0_5b_trajectory.future_pull_strength_perthou ≤ 2000 := by
  decide

/-- Concrete bound for compression_uncertainty: 0 + 1000 ≤ 2000. -/
theorem compression_uncertainty_total_pull_bounded :
    compression_uncertainty_trajectory.past_pull_strength_perthou
      + compression_uncertainty_trajectory.future_pull_strength_perthou
        ≤ 2000 := by
  decide

-- ══════════════════════════════════════════════════════════
-- BRIDGE TO RetrocausalAttractorFixedPoint
-- ══════════════════════════════════════════════════════════

/-- DOCUMENTATION THEOREM (no formal-API bridge attempted).

    The `future_pull_strength_perthou` field of a `ClaimTrajectory`
    is intended to be the contraction-strength dial of the
    `attractorStep` in `Gnosis.RetrocausalAttractorFixedPoint`.

    Recall that module's surface:

      • A `RetrocausalAttractorEvent` packages a memoized
        `future_output : VectorState` together with the cache
        retention and reconstruction witnesses.

      • `attractorStep event state := if eventRealizes event then
        event.debt.future_output else state`.

      • `realized_event_has_unique_fixed_point` shows that once
        realization fires, the dynamics collapse onto the unique
        memoized future.

    Under the chaos-order reading:

      • `future_pull_strength_perthou = 1000` corresponds to the
        regime where `eventRealizes event` holds — the
        `attractorStep` IS pulling the present onto the memoized
        future at full strength.

      • `future_pull_strength_perthou = 0` corresponds to the
        regime where `attractorStep event state = state` — the
        present is unaffected by any future pull.

    A formal Prop-level bridge would require lifting a
    `RetrocausalAttractorEvent` into a `ClaimTrajectory` and
    showing that `eventRealizes` is reflected in
    `at_theory_attractor`. We DO NOT attempt that bridge here
    because the upstream `VectorState` / `TopologicalDebt` types
    live behind `noncomputable` machinery and the goal of this
    module is `decide`-checked dynamics. The correspondence is
    recorded as documentation only. -/
theorem future_pull_corresponds_to_attractorStep_strength :
    ∀ t : ClaimTrajectory,
      t.future_pull_strength_perthou = 1000 → at_theory_attractor t := by
  intro t h
  exact theory_attractor_is_future_pull_at_max t h

/-- Symmetric documentation theorem for the past-chaos side.

    `past_pull_strength_perthou = 1000` corresponds to the
    pre-realization vacuum regime: the trajectory is at the
    `VacuousNoExperimentSpecified` floor of the AntiTheory
    ledger, with no methodology pinned and no measurement
    event yet recorded. -/
theorem past_pull_corresponds_to_vacuum_regime :
    ∀ t : ClaimTrajectory,
      t.past_pull_strength_perthou = 1000 → at_vacuum_repeller t := by
  intro t h
  exact vacuum_repeller_is_past_pull_at_max t h

end ChaosOrderDuality
end Gnosis
