/-
  VacuumToFalsificationLift.lean
  ==============================

  THE OPERATIONAL LIFT PATH FROM THE BULE VACUUM TO DEFINITE STATES.

  Companion to `NoCloningTaxEqualsBuleCost.lean` (which formalizes the
  quantum / anti-theory / bule unification at the COST level). Where that
  module sets the price tag, this module formalizes the CHAIN of lifts:
  how a claim travels from the bule vacuum (`VacuousNoExperimentSpecified`,
  the empirical-side face of `vacuumBuleUnit`) through to definite states
  (`FalsifiedByMeasurement` or `NotYetFalsified`).

  The thesis of the module:

    Every empirical claim in the ledger BEGINS at the vacuum. To get
    anywhere else, the claim must pay bule for each state transition.
    Every transition is a measurement event; every measurement event
    is +1 bule. There is no refund for retraction: a wave-N claim that
    is later corrected back to vacuum still owes the +1 bule for the
    correction itself, because the correction is itself a measurement.

  Therefore, the bule a claim has paid IS the measurement budget that has
  been spent on it. Cheap claims (one bule paid) carry less methodological
  weight than expensive ones (two bule, including a retraction); the
  runtime's "trust in a claim" should be a function of its bule history,
  not just its current status.

  Three concrete lift paths from the live ledger are formalized here:

    * `qwen_coder_7b_lift` — wave 3 lifted to `NotYetFalsified`, wave 4
      knocked it down to `FalsifiedByMeasurement`. Two lifts, bule_cost = 2.
    * `llama_1b_lift`     — wave 3 lifted to `NotYetFalsified`, wave 8
      retracted back to `VacuousNoExperimentSpecified` (anti-theory
      correction). Still two transitions, bule_cost = 2; the retraction
      is a measurement, not a refund.
    * `qwen_0_5b_lift`    — wave 1 lifted to `NotYetFalsified`. One lift,
      bule_cost = 1. The cleanest history on the ledger.

  The bridge to `Gnosis.SpectralNoiseEquilibrium` is honest: each
  `LiftPath` of `bule_cost = n` corresponds to `repeatedLift` from
  `vacuumBuleUnit` along the `.opportunity` face exactly `n` times,
  with `buleyUnitScore = n`. This is the single API surface the existing
  Bule infrastructure exposes that matches our cost semantics.

  Imports `Gnosis.SpectralNoiseEquilibrium` and `Gnosis.AntiTheory` only.
  `MeasurementEvent` is defined inline (the parallel
  `NoCloningTaxEqualsBuleCost` module may not exist at build time).

  Zero `sorry`, zero new `axiom`.
-/

import Gnosis.SpectralNoiseEquilibrium
import Gnosis.AntiTheory

namespace Gnosis
namespace VacuumToFalsificationLift

open Gnosis.SpectralNoiseEquilibrium
open Gnosis.AntiTheory

-- ══════════════════════════════════════════════════════════
-- INLINE MEASUREMENT EVENT
-- (Parallel `NoCloningTaxEqualsBuleCost` may not exist at build time;
-- we keep this module self-contained.)
-- ══════════════════════════════════════════════════════════

/-- A single measurement event recorded against a claim. The
    `wave_number` pins the wave it came from; the witness/refuting
    counts state whether the measurement supports or refutes the
    claim. Every measurement event costs +1 bule in this calculus. -/
structure MeasurementEvent where
  wave_number       : Nat
  supporting_count  : Nat
  refuting_count    : Nat
  deriving Repr, DecidableEq

/-- The total observation count of a measurement event. A
    well-formed measurement has at least one observation (otherwise
    nothing was measured). -/
def MeasurementEvent.witnessCount (m : MeasurementEvent) : Nat :=
  m.supporting_count + m.refuting_count

/-- A measurement event has at least one witness iff its total
    observation count is positive. -/
def MeasurementEvent.hasWitness (m : MeasurementEvent) : Bool :=
  decide (m.witnessCount > 0)

-- ══════════════════════════════════════════════════════════
-- LIFT PATH STRUCTURE
-- ══════════════════════════════════════════════════════════

/-- The operational record of a claim's journey from the bule vacuum
    to its current resting state.

    Fields:
      • `origin`              — typically `VacuousNoExperimentSpecified`,
        the empirical-side face of `vacuumBuleUnit`. The universal
        prior for empirical claims under the Anti-Theory turn.
      • `terminus`            — the current resting state. Typically
        `NotYetFalsified` or `FalsifiedByMeasurement`; may also be
        `VacuousNoExperimentSpecified` if a wave-N retraction has
        sent the claim back to vacuum.
      • `intermediate_states` — the chain of states traversed,
        including the terminus as the LAST element. This is the
        history the runtime can replay.
      • `bule_cost`           — the total bule paid across all
        transitions. By the calculus: one bule per state change.
      • `terminating_measurement` — the wave-numbered measurement
        event that produced the terminus. Carries the supporting/
        refuting witness counts so the claim's evidence is on the
        record. -/
structure LiftPath where
  origin                  : EmpiricalClaimStatus
  terminus                : EmpiricalClaimStatus
  intermediate_states     : List EmpiricalClaimStatus
  bule_cost               : Nat
  terminating_measurement : MeasurementEvent
  deriving Repr

-- ══════════════════════════════════════════════════════════
-- WELL-FORMEDNESS PREDICATE
-- ══════════════════════════════════════════════════════════

/-- Is this `LiftPath` well-formed?

    A path is well-formed iff:
      (1) the chain begins with the path's `origin`,
      (2) the chain ends with the path's `terminus`,
      (3) the bule_cost equals the number of transitions, which equals
          the chain length minus one (origin is free; each step costs +1),
      (4) the terminating measurement event has at least one observation
          (no measurement → no transition → no terminus).

    We deliberately do NOT enforce a per-step "valid clinamen-lift
    transition" predicate on `EmpiricalClaimStatus` itself: in this
    calculus ANY state-to-state transition is a clinamen lift, and the
    bule cost is +1 per transition regardless of the start/end faces.
    The cost semantics live entirely in the count of transitions. -/
def is_well_formed_lift (p : LiftPath) : Bool :=
  match p.intermediate_states with
  | []      => false
  | x :: xs =>
    decide (x = p.origin)
      && decide ((x :: xs).getLast (by intro h; cases h) = p.terminus)
      && decide (p.bule_cost + 1 = (x :: xs).length)
      && p.terminating_measurement.hasWitness

-- ══════════════════════════════════════════════════════════
-- THE THREE PER-INSTANCE LIFT PATHS FROM THE LIVE LEDGER
-- ══════════════════════════════════════════════════════════

/-- Qwen-Coder-7B's lift: vacuum → wave-3 `NotYetFalsified` (PCA-K=5
    PROJECTED CERTIFIED) → wave-4 `FalsifiedByMeasurement` (cross-model
    measurement refuted the projection).

    Two transitions, two bule paid. Wave-4's measurement was the
    one-counterexample event that flipped the verdict. -/
def qwen_coder_7b_lift : LiftPath :=
  { origin              := .VacuousNoExperimentSpecified
  , terminus            := .FalsifiedByMeasurement
  , intermediate_states :=
      [ .VacuousNoExperimentSpecified
      , .NotYetFalsified
      , .FalsifiedByMeasurement ]
  , bule_cost           := 2
  , terminating_measurement :=
      { wave_number      := 4
      , supporting_count := 0
      , refuting_count   := 1 } }

/-- Llama-1B's lift: vacuum → wave-3 `NotYetFalsified` (PROJECTED
    CERTIFIED) → wave-8 `VacuousNoExperimentSpecified` (anti-theory
    CORRECTION: methodology depinned on review).

    Two transitions, two bule paid. The wave-8 retraction is a
    BACKWARD correction in state-space, but it is still a measurement
    event and it still costs +1 bule. There is no refund for retraction
    in this calculus. -/
def llama_1b_lift : LiftPath :=
  { origin              := .VacuousNoExperimentSpecified
  , terminus            := .VacuousNoExperimentSpecified
  , intermediate_states :=
      [ .VacuousNoExperimentSpecified
      , .NotYetFalsified
      , .VacuousNoExperimentSpecified ]
  , bule_cost           := 2
  , terminating_measurement :=
      { wave_number      := 8
      , supporting_count := 0
      , refuting_count   := 1 } }

/-- Qwen-0.5B's lift: vacuum → wave-1 `NotYetFalsified` (one
    methodology-pinned measurement supported the claim).

    One transition, one bule paid. The cleanest history on the
    ledger; no further state change has happened. -/
def qwen_0_5b_lift : LiftPath :=
  { origin              := .VacuousNoExperimentSpecified
  , terminus            := .NotYetFalsified
  , intermediate_states :=
      [ .VacuousNoExperimentSpecified
      , .NotYetFalsified ]
  , bule_cost           := 1
  , terminating_measurement :=
      { wave_number      := 1
      , supporting_count := 1
      , refuting_count   := 0 } }

-- ══════════════════════════════════════════════════════════
-- WELL-FORMEDNESS THEOREMS
-- ══════════════════════════════════════════════════════════

/-- Qwen-Coder-7B's lift path is well-formed: chain
    `[Vacuous, NotYetFalsified, FalsifiedByMeasurement]`,
    bule_cost = 2, refuting_count = 1. -/
theorem qwen_coder_7b_lift_well_formed :
    is_well_formed_lift qwen_coder_7b_lift = true := by
  decide

/-- Llama-1B's lift path is well-formed: chain
    `[Vacuous, NotYetFalsified, Vacuous]` (the wave-8 retraction
    closes the loop), bule_cost = 2, refuting_count = 1. -/
theorem llama_1b_lift_well_formed :
    is_well_formed_lift llama_1b_lift = true := by
  decide

/-- Qwen-0.5B's lift path is well-formed: chain
    `[Vacuous, NotYetFalsified]`, bule_cost = 1,
    supporting_count = 1. -/
theorem qwen_0_5b_lift_well_formed :
    is_well_formed_lift qwen_0_5b_lift = true := by
  decide

-- ══════════════════════════════════════════════════════════
-- THE CHEAPEST HISTORY: QWEN-0.5B
-- ══════════════════════════════════════════════════════════

/-- Qwen-0.5B paid the LEAST bule of the three: its lift cost (1) is
    strictly less than both Qwen-Coder-7B's (2) and Llama-1B's (2).
    The cleanest history on the ledger. -/
theorem qwen_0_5b_paid_least_bule :
    qwen_0_5b_lift.bule_cost < qwen_coder_7b_lift.bule_cost ∧
    qwen_0_5b_lift.bule_cost < llama_1b_lift.bule_cost := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- THE VACUUM IS THE UNIVERSAL ORIGIN
-- ══════════════════════════════════════════════════════════

/-- THE LOAD-BEARING CLAIM OF THIS MODULE.

    Every recorded claim's `origin` is `VacuousNoExperimentSpecified`.
    The bule vacuum is the universal prior for empirical claims under
    the Anti-Theory turn: nothing arrives pre-falsified, pre-certified,
    or pre-anything. Every claim begins where the calculus begins —
    at the vacuum face, score zero, methodology unpinned. -/
theorem every_claim_starts_at_vacuum :
    qwen_coder_7b_lift.origin = .VacuousNoExperimentSpecified ∧
    llama_1b_lift.origin       = .VacuousNoExperimentSpecified ∧
    qwen_0_5b_lift.origin      = .VacuousNoExperimentSpecified := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- CORRECTION COSTS ADDITIONAL BULE (THE NO-REFUND THEOREM)
-- ══════════════════════════════════════════════════════════

/-- THE NO-REFUND THEOREM.

    Llama-1B's wave-8 correction sent the claim from `NotYetFalsified`
    BACK to `VacuousNoExperimentSpecified`. In a naive accounting one
    might expect the correction to "cancel" the wave-3 lift and leave
    the claim with bule_cost = 0. It does not. The correction is itself
    a measurement event — the wave-8 review IS the act that depinned
    the methodology — and so it costs +1 additional bule.

    The total bule paid by `llama_1b_lift` is therefore 2, not 0. The
    runtime accounting must treat this as a CORRECTION lift, not a
    knowledge lift, but the measurement budget that has been spent on
    the claim is still 2 bule, and that is what determines the
    methodological weight of its (now-vacuous) status. -/
theorem correction_costs_additional_bule :
    llama_1b_lift.bule_cost = 2 ∧
    llama_1b_lift.terminus = .VacuousNoExperimentSpecified ∧
    llama_1b_lift.bule_cost ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- WELL-FORMED LIFTS TO DEFINITE STATES IMPLY WITNESSES
-- ══════════════════════════════════════════════════════════

/-- Helper: a definite-state terminus is one of `NotYetFalsified` or
    `FalsifiedByMeasurement` — i.e. a state for which the calculus
    requires actual evidence. (`StructuralIdentity` is not empirical;
    `VacuousNoExperimentSpecified` is the vacuum face and requires
    no witness.) -/
def is_definite_terminus : EmpiricalClaimStatus → Bool
  | .NotYetFalsified         => true
  | .FalsifiedByMeasurement  => true
  | .StructuralIdentity      => false
  | .VacuousNoExperimentSpecified => false

/-- WELL-FORMED LIFT TO A DEFINITE STATE IMPLIES A WITNESSED
    TERMINATING MEASUREMENT.

    For any well-formed `LiftPath`, the terminating measurement event
    has at least one observation (`witnessCount > 0`). This is the
    formal expression of "you cannot lift to `NotYetFalsified` or
    `FalsifiedByMeasurement` without paying for evidence". The lemma
    is stated for ANY well-formed lift (because well-formedness already
    requires `hasWitness`), so it holds automatically for definite-state
    termini in particular. -/
theorem well_formed_lift_terminus_has_witness_for_terminus
    (p : LiftPath) (h : is_well_formed_lift p = true) :
    p.terminating_measurement.witnessCount > 0 := by
  unfold is_well_formed_lift at h
  cases hxs : p.intermediate_states with
  | nil =>
      rw [hxs] at h
      simp at h
  | cons x xs =>
      rw [hxs] at h
      -- The conjunction's last clause is hasWitness = true.
      -- Extract it: h has shape (... && hasWitness) = true
      have hWit : p.terminating_measurement.hasWitness = true := by
        have := h
        -- Decompose the four-way Bool conjunction.
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.2
      -- hasWitness = true unfolds to decide (witnessCount > 0)
      unfold MeasurementEvent.hasWitness at hWit
      exact of_decide_eq_true hWit

/-- Companion: each of the three concrete lift paths in this module
    has a witnessed terminating measurement. Direct computational
    consequence of the three well-formedness theorems. -/
theorem all_three_lifts_have_witnessed_termini :
    qwen_coder_7b_lift.terminating_measurement.witnessCount > 0 ∧
    llama_1b_lift.terminating_measurement.witnessCount       > 0 ∧
    qwen_0_5b_lift.terminating_measurement.witnessCount      > 0 := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- THE BRIDGE TO SPECTRAL-NOISE-EQUILIBRIUM (BULEYUNIT)
-- ══════════════════════════════════════════════════════════

/-- The bridge mapping: a `LiftPath` of `bule_cost = n` corresponds to
    `repeatedLift vacuumBuleUnit .opportunity n` — the canonical
    `BuleyUnit` reached from the vacuum by `n` clinamen lifts on the
    `opportunity` face.

    We choose the `opportunity` face because the empirical lift is
    "lifting an unspent measurement opportunity into a measurement-
    pinned claim"; the `waste` and `diversity` faces are reserved for
    thermodynamic and protocol-spread accounting respectively. The
    choice is a runtime convention; the cost theorem below holds
    independent of which single face is chosen because `repeatedLift`
    on any single face increments `buleyUnitScore` by exactly +1
    per step (`clinamen_lift_score_strict_increment`). -/
def buleUnitOfLiftPath (p : LiftPath) : BuleyUnit :=
  repeatedLift vacuumBuleUnit BuleyFace.opportunity p.bule_cost

/-- THE BRIDGE THEOREM.

    The `bule_cost` of any `LiftPath` equals the `buleyUnitScore` of
    the `BuleyUnit` reached by walking the chain of clinamen lifts
    from the vacuum.

    This is the link between the operational ledger ("how many
    measurements has this claim paid for?") and the underlying Bule
    calculus ("how far from vacuum is its BuleyUnit?"). They agree
    by construction.

    Proof: `repeated_lift_score` from `SpectralNoiseEquilibrium` plus
    `vacuum_has_zero_score`. -/
theorem lift_path_corresponds_to_clinamen_chain (p : LiftPath) :
    buleyUnitScore (buleUnitOfLiftPath p) = p.bule_cost := by
  unfold buleUnitOfLiftPath
  rw [repeated_lift_score]
  rw [vacuum_has_zero_score]
  -- 0 + p.bule_cost = p.bule_cost
  exact Nat.zero_add p.bule_cost

/-- Pointwise corollary: each of the three concrete lift paths has its
    `bule_cost` equal to the `buleyUnitScore` of its image `BuleyUnit`.
    Computational decoration on `lift_path_corresponds_to_clinamen_chain`. -/
theorem three_lifts_match_buley_score :
    buleyUnitScore (buleUnitOfLiftPath qwen_coder_7b_lift) = 2 ∧
    buleyUnitScore (buleUnitOfLiftPath llama_1b_lift)       = 2 ∧
    buleyUnitScore (buleUnitOfLiftPath qwen_0_5b_lift)      = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [lift_path_corresponds_to_clinamen_chain]; rfl
  · rw [lift_path_corresponds_to_clinamen_chain]; rfl
  · rw [lift_path_corresponds_to_clinamen_chain]; rfl

/-- Final summary of bule history across the three claims (decided).
    The runtime can read this off and rank claims by methodological
    weight: Qwen-Coder-7B and Llama-1B carry 2 bule of measurement
    history each (one a falsification, the other a retraction);
    Qwen-0.5B carries 1 bule (a single supporting measurement). -/
theorem ledger_bule_summary :
    qwen_coder_7b_lift.bule_cost = 2 ∧
    llama_1b_lift.bule_cost       = 2 ∧
    qwen_0_5b_lift.bule_cost      = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

end VacuumToFalsificationLift
end Gnosis
