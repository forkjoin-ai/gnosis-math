/-
  ConjectureAsCommitment.lean
  ===========================

  ANTI-THEORY'S COMMITMENT RULE.

  "Speak conjectures only with commitments. A conjecture without a
  commitment to test it is not a conjecture; it is wishful thinking
  pretending to be science. The Lean predicate
  `is_scientifically_meaningful_with_commitment` is the run-time check
  that future agents apply when adding new conjectures to the stack."

  ----------------------------------------------------------------
  WHY THIS MODULE EXISTS
  ----------------------------------------------------------------

  Anti-theory's load-bearing claim: a conjecture has scientific content
  iff it specifies AND COMMITS TO running a specific falsifying
  experiment. A conjecture without a commitment to test it is vacuous
  — indistinguishable from an opinion, a hope, a marketing claim.

  Three failure modes the predicate refuses:

    (V1) The conjecture has a beautiful claim and no experiment.
         "X scales gracefully" with no measurement design = vacuous.

    (V2) The conjecture has an experiment design that nobody owns.
         A scope doc on a wiki is not a commitment; an engineer-hours
         allocation is.

    (V3) The conjecture has a commitment with empty experiment text.
         A bare "we will measure something" is not a falsifier.

  The decision procedure is `decide`-checked and runs at compile time.

  ----------------------------------------------------------------
  COMPANION FILES
  ----------------------------------------------------------------

  Parallel modules `Gnosis.AntiTheory`, `Gnosis.FalsificationLedger`,
  and `Gnosis.ProvisionalCertificate` may exist (or may not yet exist).
  This file does NOT depend on them — the structures it needs are
  defined inline so the build is self-contained.

  Init-only Lean 4. Zero sorries, zero axioms.
-/

namespace Gnosis
namespace ConjectureAsCommitment

-- ══════════════════════════════════════════════════════════
-- 1. THE COMMITMENT STRUCTURE
-- ══════════════════════════════════════════════════════════

/-- A `Commitment` is a concrete, scoped, ownable plan to run a
    falsifying experiment for a specific conjecture.

    Fields:

    * `experiment_description` — plain-language, single-sentence
      description of the test. Empty string = the commitment is
      a placeholder, NOT a falsifier (see `is_scientifically_meaningful_with_commitment`).

    * `expected_runtime_minutes` — the compute / wall-clock budget
      the test will consume on the assigned wave's hardware.
      Used by the wave scheduler to fit experiments in a sprint.

    * `required_artifacts` — the files / binaries / data shards
      that must be in place before the test can run. Surfaced so
      a wave can fail fast if an artifact is missing.

    * `assignable_to_wave` — the index of the future wave that
      will execute the commitment. A commitment without a wave
      assignment is a wish; a commitment with a wave assignment
      is a falsifier-in-flight. -/
structure Commitment where
  experiment_description   : String
  expected_runtime_minutes : Nat
  required_artifacts       : List String
  assignable_to_wave       : Nat
  deriving Repr

-- ══════════════════════════════════════════════════════════
-- 2. THE CONJECTURE STRUCTURE
-- ══════════════════════════════════════════════════════════

/-- A `Conjecture` is a falsifiable claim ABOUT a system, paired
    with a specific commitment to run the experiment that would
    falsify it.

    Fields:

    * `claim_text` — human-readable claim. Required for the
      ledger record but not used by the meaningfulness predicate.

    * `claim_predicate_name` — the symbolic name of the predicate
      the claim quantifies (e.g. "rank_density_invariant"). Used
      by downstream tooling to wire conjectures to measurement
      pipelines.

    * `falsifying_commitment` — the embedded `Commitment`. If this
      commitment has empty experiment text, the conjecture is
      vacuous regardless of how strongly the claim is asserted.

    * `is_committed` — does some named owner OWN running this
      experiment in the assigned wave? `false` here downgrades the
      conjecture to wishful thinking even if the description is
      perfect. -/
structure Conjecture where
  claim_text             : String
  claim_predicate_name   : String
  falsifying_commitment  : Commitment
  is_committed           : Bool
  deriving Repr

-- ══════════════════════════════════════════════════════════
-- 3. THE MEANINGFULNESS PREDICATE
-- ══════════════════════════════════════════════════════════

/-- A conjecture is scientifically meaningful WITH commitment iff:
      (a) someone OWNS running the experiment (`is_committed = true`), AND
      (b) the embedded commitment carries a non-empty experiment
          description.

    Both must hold. Either alone is decoration. Both together is
    a falsifiable claim with an honest falsifier on the runway. -/
def is_scientifically_meaningful_with_commitment (c : Conjecture) : Bool :=
  c.is_committed && c.falsifying_commitment.experiment_description ≠ ""

-- ══════════════════════════════════════════════════════════
-- 4. THE FOUR CURRENT OPEN CONJECTURES (state as of 2026-05-03)
-- ══════════════════════════════════════════════════════════

/-- C1 — K-WIDENING RESCUES AT SCALE.

    Claim: "If K is increased linearly with hidden_dim, F_eff is
    restored." Commitment: a K-sweep on Qwen-Coder-7B at K ∈
    {5, 10, 20, 50, 100, 200}. Owned by wave 7. Currently in flight. -/
def c1_K_widening_rescues_at_scale : Conjecture :=
  { claim_text :=
      "If K is increased linearly with hidden_dim, F_eff is restored"
  , claim_predicate_name := "K_widening_rescues_F_eff"
  , falsifying_commitment :=
      { experiment_description :=
          "K-sweep on Qwen-Coder-7B at K∈{5,10,20,50,100,200}"
      , expected_runtime_minutes := 10
      , required_artifacts :=
          [ "draft-and-verify"
          , "qwen-coder-7b.knot"
          , "qwen-coder-7b.pca" ]
      , assignable_to_wave := 7 }
  , is_committed := true }

/-- C2 — RANDOM PROJECTION COMPETITIVE WITH PCA.

    Claim: "Random Gaussian projection achieves equal cosine to
    PCA at the same k." Commitment: a synthetic experiment that
    pits PCA against random projection at k ∈ {8, 32, 128}. Owned
    by wave 7. -/
def c2_random_projection_competitive_with_PCA : Conjecture :=
  { claim_text :=
      "Random Gaussian projection achieves equal cosine to PCA at same k"
  , claim_predicate_name := "random_projection_matches_PCA_cosine"
  , falsifying_commitment :=
      { experiment_description :=
          "synthetic experiment with PCA vs random at k=8,32,128"
      , expected_runtime_minutes := 10
      , required_artifacts := [ "python3" , "numpy" ]
      , assignable_to_wave := 7 }
  , is_committed := true }

/-- C3 — METHODOLOGY RECONCILIATION RESOLVES F3.

    Claim: "Wave-5 vs wave-6 disagreement is fully explained by
    --coverage semantics." Commitment: controlled cosine measurement
    at coverage levels 0.50, 0.90, and 1.00. Owned by wave 7. -/
def c3_methodology_reconciliation_resolves_F3 : Conjecture :=
  { claim_text :=
      "Wave-5 vs wave-6 disagreement is fully explained by --coverage semantics"
  , claim_predicate_name := "coverage_semantics_explains_F3_disagreement"
  , falsifying_commitment :=
      { experiment_description :=
          "controlled cosine measurement at coverage 0.50, 0.90, 1.00"
      , expected_runtime_minutes := 8
      , required_artifacts :=
          [ "standing-wave-pca" , "qwen-0.5b knot" ]
      , assignable_to_wave := 7 }
  , is_committed := true }

/-- C4 — AETHER-FLOW COMPRESSED WIRE FORMAT.

    Claim: "4-byte tagged PCA residual wire codec preserves
    Qwen-0.5B fidelity over network." A scope document exists; no
    engineer is yet assigned. The commitment has shape (description,
    runtime, artifacts, wave 12+) but `is_committed = false`. The
    meaningfulness predicate returns `false`. -/
def c4_aether_flow_compressed_wire_format : Conjecture :=
  { claim_text :=
      "4-byte tagged PCA residual wire codec preserves Qwen-0.5B fidelity over network"
  , claim_predicate_name := "aether_flow_compressed_codec_preserves_fidelity"
  , falsifying_commitment :=
      { experiment_description :=
          "implement codec, smoke-test single-host loop"
      , expected_runtime_minutes := 600
      , required_artifacts :=
          [ "Rust codec" , "TS encoder" , "version negotiation" ]
      , assignable_to_wave := 12 }
  , is_committed := false }

-- ══════════════════════════════════════════════════════════
-- 5. PER-INSTANCE MEANINGFULNESS THEOREMS
-- ══════════════════════════════════════════════════════════

/-- C1 is scientifically meaningful: committed + non-empty experiment. -/
theorem c1_is_scientifically_meaningful :
    is_scientifically_meaningful_with_commitment
        c1_K_widening_rescues_at_scale = true := by
  decide

/-- C2 is scientifically meaningful: committed + non-empty experiment. -/
theorem c2_is_scientifically_meaningful :
    is_scientifically_meaningful_with_commitment
        c2_random_projection_competitive_with_PCA = true := by
  decide

/-- C3 is scientifically meaningful: committed + non-empty experiment. -/
theorem c3_is_scientifically_meaningful :
    is_scientifically_meaningful_with_commitment
        c3_methodology_reconciliation_resolves_F3 = true := by
  decide

/-- C4 is NOT scientifically meaningful — uncommitted, so vacuous
    even though it carries a non-empty experiment description. The
    description without an owner is wishful thinking. -/
theorem c4_is_NOT_scientifically_meaningful :
    is_scientifically_meaningful_with_commitment
        c4_aether_flow_compressed_wire_format = false := by
  decide

-- ══════════════════════════════════════════════════════════
-- 6. THE COMMITMENT-HONESTY THEOREMS
-- ══════════════════════════════════════════════════════════

/-- The full open ledger as of 2026-05-03. Order is preserved; the
    list is the canonical sequence the wave scheduler reads. -/
def open_ledger : List Conjecture :=
  [ c1_K_widening_rescues_at_scale
  , c2_random_projection_competitive_with_PCA
  , c3_methodology_reconciliation_resolves_F3
  , c4_aether_flow_compressed_wire_format ]

/-- The count of meaningfully-committed conjectures in the open ledger. -/
def committed_conjecture_count : Nat :=
  (open_ledger.filter is_scientifically_meaningful_with_commitment).length

/-- COMMITMENT-HONESTY THEOREM 1.

    The open ledger holds exactly THREE scientifically-meaningful,
    committed conjectures (C1, C2, C3) and ONE uncommitted one (C4).
    The split is decide-checked against the per-instance commitments
    declared above. -/
theorem committed_conjecture_count_is_three :
    committed_conjecture_count = 3 := by
  decide

/-- COMMITMENT-HONESTY THEOREM 2.

    C4 reads as vacuous until someone commits to running the
    experiment. The scope doc exists, the description is non-empty,
    the wave is even tentatively assigned (12+). None of that
    matters: without `is_committed = true` the predicate refuses
    to call the conjecture science. -/
theorem uncommitted_conjecture_is_vacuous :
    is_scientifically_meaningful_with_commitment
        c4_aether_flow_compressed_wire_format = false := by
  decide

-- ══════════════════════════════════════════════════════════
-- 7. THE FUTURE-WAVE ROSTER
-- ══════════════════════════════════════════════════════════

/-- The conjectures wave 7 has agreed to run. C4 is excluded
    because no engineer has accepted ownership; it stays on the
    backlog until promoted. -/
def wave_7_responsible_for : List Conjecture :=
  [ c1_K_widening_rescues_at_scale
  , c2_random_projection_competitive_with_PCA
  , c3_methodology_reconciliation_resolves_F3 ]

/-- All entries in `wave_7_responsible_for` are scientifically
    meaningful AND assigned to wave 7. -/
def all_wave_7_committed : Bool :=
  wave_7_responsible_for.all
    (fun c => is_scientifically_meaningful_with_commitment c
              && decide (c.falsifying_commitment.assignable_to_wave = 7))

/-- WAVE-7 ROSTER THEOREM.

    Wave 7 carries exactly three falsifiable commitments — C1, C2,
    C3 — and every entry on the roster passes the meaningfulness
    predicate AND is wave-7-assigned. -/
theorem wave_7_carries_three_falsifiable_commitments :
    wave_7_responsible_for.length = 3
      ∧ all_wave_7_committed = true := by
  refine And.intro ?_ ?_
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- 8. PROMOTION / DEMOTION RULES
-- ══════════════════════════════════════════════════════════

/-- A `MeasurementSupport` record is a single piece of evidence a
    conjecture is currently surviving falsification: the methodology
    that produced it (so we can audit method-diversity) and the
    binary outcome (true = supported, false = inconclusive). -/
structure MeasurementSupport where
  methodology_name : String
  supports_claim   : Bool
  deriving Repr

/-- The supports-this-conjecture ledger. As of 2026-05-03 every
    open conjecture has zero replicated supports; we record this
    honestly rather than padding. -/
def supports_for : Conjecture → List MeasurementSupport
  | _ => []

/-- A conjecture promotes (to "structural-style, still revocable,
    treated as load-bearing in policy decisions") iff it has at
    least 3 supporting measurements drawn from at least 3 DISTINCT
    methodologies. The predicate counts unique methodology names
    among supports whose `supports_claim = true`. -/
def conjecture_promotes_on_replicated_support (c : Conjecture) : Bool :=
  let positives :=
    (supports_for c).filter (fun m => m.supports_claim)
  let names := positives.map (fun m => m.methodology_name)
  let unique_names := names.eraseDups
  decide (unique_names.length ≥ 3)

/-- HONEST RECORD: none of the four open conjectures currently
    qualify for promotion. The supports ledger is empty for every
    `c ∈ open_ledger`. -/
theorem no_open_conjecture_currently_promotes :
    open_ledger.all
      (fun c => conjecture_promotes_on_replicated_support c = false)
      = true := by
  decide

/-- The status of a conjecture relative to its falsifier history. -/
inductive ConjectureFalsificationState
  | NotYetFalsified
  | FalsifiedByMeasurement
  deriving DecidableEq, Repr

/-- Demotion rule: any single methodologically-pinned counterexample
    flips a `NotYetFalsified` conjecture to `FalsifiedByMeasurement`,
    permanently. Once demoted, a conjecture cannot be revived by
    later supportive measurements — the falsifier is load-bearing
    history.

    Inputs:
      * current state of the conjecture
      * `pinned_counterexample` — true iff a wave produced a
        replicable counterexample with a named methodology

    Output: the new state. The function is monotonic toward
    falsification: once `FalsifiedByMeasurement`, stays there. -/
def conjecture_demotes_on_falsification
    (state : ConjectureFalsificationState)
    (pinned_counterexample : Bool) : ConjectureFalsificationState :=
  match state with
  | .FalsifiedByMeasurement => .FalsifiedByMeasurement
  | .NotYetFalsified =>
      if pinned_counterexample then .FalsifiedByMeasurement
      else .NotYetFalsified

/-- DEMOTION-IS-PERMANENT THEOREM.

    Once a conjecture has been demoted to `FalsifiedByMeasurement`,
    no subsequent input — supportive or counter — restores it to
    `NotYetFalsified`. The demotion is one-way. -/
theorem demotion_is_permanent (b : Bool) :
    conjecture_demotes_on_falsification .FalsifiedByMeasurement b
      = .FalsifiedByMeasurement := by
  cases b <;> rfl

/-- DEMOTION-FIRES-ON-COUNTEREXAMPLE THEOREM.

    A `NotYetFalsified` conjecture flips to `FalsifiedByMeasurement`
    the instant a methodologically-pinned counterexample is
    presented. -/
theorem demotion_fires_on_counterexample :
    conjecture_demotes_on_falsification .NotYetFalsified true
      = .FalsifiedByMeasurement := by
  rfl

/-- NO-SPONTANEOUS-DEMOTION THEOREM.

    A `NotYetFalsified` conjecture stays `NotYetFalsified` when no
    counterexample has been pinned. Absence of evidence is not a
    falsifier. -/
theorem no_spontaneous_demotion :
    conjecture_demotes_on_falsification .NotYetFalsified false
      = .NotYetFalsified := by
  rfl

end ConjectureAsCommitment
end Gnosis
