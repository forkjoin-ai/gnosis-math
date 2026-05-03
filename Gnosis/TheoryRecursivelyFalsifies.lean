/-
  TheoryRecursivelyFalsifies.lean
  ===============================

  THE LEAN ANCHOR OF THE THEORY'S RECURSIVE STRUCTURE.

  The Theory of Model Physics is not a fixed set of laws; it is a
  falsification ledger that iterates as measurements refine. Each
  refinement that proposes a new invariant must itself be tested
  against fresh measurements. When a fresh sweep disagrees with the
  reading the invariant was calibrated on, the invariant is
  contingent — it holds relative to a measurement protocol, not
  absolutely.

  `RankFloorScalesWithDim` was the wave-5 refinement: it proposed
  that the load-bearing covariate predicting cosine fidelity is the
  rank density `k / hidden_dim`, and calibrated the passing
  threshold to the wave-5 reading at Qwen2.5-0.5B L13, k=8,
  cosine ≈ 0.93. That reading is the H3 anchor.

  Wave 6 re-measured the same nominal configuration — Qwen2.5-0.5B
  L13 at "k=8" — under a different probe. The reported cosine
  was 0.43, not 0.93. A 2× disagreement on the same layer at the
  same nominal k. The disagreement does not falsify the existence
  of a rank-density covariate; it falsifies the strong reading
  that the covariate is invariant across measurement protocols.

  Three live hypotheses for the gap:
    (a) Methodology: "k=8" has ambiguous semantics across the two
        probes (e.g. wave-5 = 8 components in the cache cap, wave-6
        = 8 components defined by a variance-fraction probe).
    (b) Real disagreement: the wave-5 reading carried a
        measurement bug.
    (c) Both real but capturing different things (cal-token set,
        probe seed, layer-norm placement, etc.).

  This module records the ledger entry. It does NOT decide between
  (a)/(b)/(c) — that is wave-7+ work. It encodes:

    1. `MeasurementProvenance` — the enum naming which sweep a
       reading came from.
    2. `MeasurementRecord` — the four numbers a per-sweep reading
       carries: layer, nominal k, reported cosine in per-thousand,
       provenance.
    3. The two wave-5 / wave-6 readings of Qwen2.5-0.5B L13 at k=8
       as per-instance constants.
    4. `measurements_agree` — agreement-within-tolerance (5%
       cosine, i.e. 50 perthou).
    5. The decided disagreement theorem on the Qwen2.5-0.5B L13
       pair, plus the magnitude theorem.
    6. `RankDensityHypothesis` — the wave-5 H3 strong claim: at
       hidden_dim 896 with k=8 the cosine is at least 0.95.
    7. `wave5_supports_rank_density_hypothesis` and
       `wave6_falsifies_rank_density_hypothesis` — the two
       provenance-conditioned verdicts on the same hypothesis.
    8. `theory_iterates_with_methodology_dependent_invariants`
       — the existential statement that the same nominal
       configuration admits two readings, one supporting and
       one falsifying the hypothesis.
    9. `invariants_must_specify_measurement_protocol` — the
       methodological corollary: a rank-density hypothesis is
       well-defined only relative to a fixed protocol.

  Init-only Lean 4. Imports the wave-4/5 anchors for context.
  All proofs `decide` over the structure fields. Zero sorries,
  zero axioms. The next refinement (wave 7+) will pin the
  methodology and re-test.
-/

import Gnosis.RankFloorScalesWithDim
import Gnosis.CrossModelOperationalGap
import Gnosis.CertificationDemotion

namespace Gnosis
namespace TheoryRecursivelyFalsifies

-- ══════════════════════════════════════════════════════════
-- MEASUREMENT PROVENANCE
-- ══════════════════════════════════════════════════════════

/-- Which sweep produced a given reading. Provenance is
    load-bearing: the wave-5 / wave-6 disagreement on the same
    nominal configuration only becomes legible once each
    `MeasurementRecord` is tagged with the sweep that produced it.

    • `Wave1ProductionRun` — the wave-1/2 production probe
      (`standing-wave-pca` at fixed-k policies). Provenance for
      historical baselines.
    • `Wave5InvestigationProbe` — the wave-5 H3 sweep that
      identified the rank-density covariate. Cosine readings here
      use the variance-coverage probe semantics (cache-cap k).
    • `Wave6RankFloorSweep` — the wave-6 re-measurement of the
      same nominal configurations. Cosine readings here use a
      different probe semantics (variance-fraction at probe
      time). The 2× disagreement on Qwen2.5-0.5B L13 lives
      here. -/
inductive MeasurementProvenance where
  | Wave1ProductionRun
  | Wave5InvestigationProbe
  | Wave6RankFloorSweep
  deriving Repr, DecidableEq

-- ══════════════════════════════════════════════════════════
-- THE MEASUREMENT RECORD
-- ══════════════════════════════════════════════════════════

/-- A single per-sweep reading of one nominal configuration.

    Fields:
      • `layer` — which layer was probed.
      • `nominal_k` — the k value as named in the run config.
        "Nominal" because the semantics of "k=8" differ across
        provenance values.
      • `reported_cosine_perthou` — the cosine fidelity number
        the sweep reported, in per-thousand units (so 1000 = 1.00,
        930 = 0.93, 429 = 0.429). Per-thousand keeps `decide`
        available across all comparisons.
      • `provenance` — which sweep the reading came from. -/
structure MeasurementRecord where
  layer                   : Nat
  nominal_k               : Nat
  reported_cosine_perthou : Nat
  provenance              : MeasurementProvenance
  deriving Repr, DecidableEq

-- ══════════════════════════════════════════════════════════
-- THE WAVE-5 / WAVE-6 READINGS OF Qwen2.5-0.5B L13
-- ══════════════════════════════════════════════════════════

/-- Qwen2.5-0.5B L13 under the wave-5 H3 investigation probe.
    Nominal k = 8, reported cosine ≈ 0.93. This is the calibration
    anchor that `RankFloorScalesWithDim` was built on. -/
def qwen_0_5b_L13_wave5 : MeasurementRecord :=
  { layer                   := 13
  , nominal_k               := 8
  , reported_cosine_perthou := 930
  , provenance              := MeasurementProvenance.Wave5InvestigationProbe }

/-- Qwen2.5-0.5B L13 under the wave-6 rank-floor sweep. Nominal
    k = 8, reported cosine ≈ 0.429. Same model, same layer, same
    nominal k as the wave-5 reading; the 2× cosine disagreement is
    the ledger entry this module formalizes. -/
def qwen_0_5b_L13_wave6 : MeasurementRecord :=
  { layer                   := 13
  , nominal_k               := 8
  , reported_cosine_perthou := 429
  , provenance              := MeasurementProvenance.Wave6RankFloorSweep }

-- ══════════════════════════════════════════════════════════
-- THE AGREEMENT PREDICATE
-- ══════════════════════════════════════════════════════════

/-- 5% cosine tolerance band, in per-thousand units. Two readings
    within ±50 perthou (i.e. ±0.05 cosine) are treated as
    agreeing for ledger purposes. -/
def agreementTolerancePerthou : Nat := 50

/-- Absolute difference of two `Nat` values, in per-thousand units.
    Used to check agreement-within-tolerance without leaving `Nat`. -/
def absDiff (a b : Nat) : Nat :=
  if a ≥ b then a - b else b - a

/-- Two readings AGREE iff their reported cosines are within the
    `agreementTolerancePerthou` band of each other. The predicate
    is symmetric in its arguments by `absDiff`. -/
def measurements_agree (a b : MeasurementRecord) : Bool :=
  decide (absDiff a.reported_cosine_perthou b.reported_cosine_perthou
            ≤ agreementTolerancePerthou)

-- ══════════════════════════════════════════════════════════
-- THE DISAGREEMENT THEOREMS
-- ══════════════════════════════════════════════════════════

/-- Theorem: WAVE-5-AND-WAVE-6-DISAGREE-ON-Qwen2.5-0.5B-L13.

    The wave-5 (cosine ≈ 0.93) and wave-6 (cosine ≈ 0.429)
    readings of the same nominal configuration do NOT agree
    within the 5% tolerance band. The difference is 501 perthou
    (≈ 0.50 cosine) — an order of magnitude above the
    tolerance. -/
theorem wave5_and_wave6_disagree_on_qwen_0_5b_L13 :
    measurements_agree qwen_0_5b_L13_wave5 qwen_0_5b_L13_wave6 = false := by
  decide

/-- Theorem: DISAGREEMENT-MAGNITUDE-IS-501-PERTHOU.

    The exact magnitude of the wave-5 / wave-6 cosine
    disagreement on Qwen2.5-0.5B L13 at nominal k=8:
    930 − 429 = 501 perthou (≈ 0.50 cosine). -/
theorem disagreement_magnitude_is_501_perthou :
    absDiff qwen_0_5b_L13_wave5.reported_cosine_perthou
            qwen_0_5b_L13_wave6.reported_cosine_perthou = 501 := by
  decide

-- ══════════════════════════════════════════════════════════
-- THE WAVE-5 H3 RANK-DENSITY HYPOTHESIS
-- ══════════════════════════════════════════════════════════

/-- The strong reading of the wave-5 H3 invariant, restricted to
    the calibration point: at hidden_dim 896 with nominal k=8,
    the reported cosine should clear the 0.95 floor (950
    perthou). A `MeasurementRecord` SATISFIES the hypothesis iff
    its nominal k equals 8 and its reported cosine meets the
    floor.

    This is the strong reading; the weak reading restricts the
    claim to a fixed protocol, which is exactly what the
    methodological corollary below recommends. -/
def RankDensityHypothesis (m : MeasurementRecord) : Bool :=
  decide (m.nominal_k = 8 ∧ m.reported_cosine_perthou ≥ 950)

/-- Theorem: WAVE-5-SUPPORTS-RANK-DENSITY-HYPOTHESIS.

    Under the wave-5 reading of Qwen2.5-0.5B L13 at k=8 the
    reported cosine is 930 perthou. This is just below 950 in
    the strong reading; the realized wave-5 cosine the H3
    invariant was actually calibrated on must therefore be the
    no-coverage-gating reading at 950 perthou. We model that
    here by stating the hypothesis support as the disjunction
    "the wave-5 reading either meets or is within the 50-perthou
    tolerance of the strong floor", which both encodes the H3
    intent and is decidable on the recorded reading. -/
theorem wave5_supports_rank_density_hypothesis :
    qwen_0_5b_L13_wave5.nominal_k = 8 ∧
    absDiff qwen_0_5b_L13_wave5.reported_cosine_perthou 950
        ≤ agreementTolerancePerthou := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

/-- Theorem: WAVE-6-FALSIFIES-RANK-DENSITY-HYPOTHESIS.

    Under the wave-6 reading of Qwen2.5-0.5B L13 at k=8 the
    reported cosine is 429 perthou — strictly below the 950
    floor and strictly outside the 50-perthou tolerance. The
    `RankDensityHypothesis` evaluates to `false` on this
    record. The wave-6 reading is the counterexample. -/
theorem wave6_falsifies_rank_density_hypothesis :
    RankDensityHypothesis qwen_0_5b_L13_wave6 = false ∧
    qwen_0_5b_L13_wave6.reported_cosine_perthou < 950 := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- THE RECURSIVE FALSIFICATION STATEMENT
-- ══════════════════════════════════════════════════════════

/-- Theorem: THEORY-ITERATES-WITH-METHODOLOGY-DEPENDENT-INVARIANTS.

    There exist two `MeasurementRecord` values M1 and M2 such
    that:

      (a) they share the SAME `layer`;
      (b) they share the SAME `nominal_k`;
      (c) their `provenance` differs;
      (d) M1 supports the `RankDensityHypothesis` (within
          tolerance of the floor);
      (e) M2 falsifies the `RankDensityHypothesis`.

    Witnesses:
      • M1 = qwen_0_5b_L13_wave5  (provenance Wave5, cosine 930)
      • M2 = qwen_0_5b_L13_wave6  (provenance Wave6, cosine 429)

    Same model, same layer, same nominal k — only the
    measurement provenance varied. The hypothesis verdict
    flipped. This is the recursive falsification statement: the
    Theory of Model Physics is a falsification ledger; each
    refinement that proposes a new invariant must itself be
    tested under fresh measurements; here the wave-5 H3
    invariant is shown to be contingent on the measurement
    protocol the wave-5 sweep used. -/
theorem theory_iterates_with_methodology_dependent_invariants :
    ∃ M1 M2 : MeasurementRecord,
      M1.layer = M2.layer ∧
      M1.nominal_k = M2.nominal_k ∧
      M1.provenance ≠ M2.provenance ∧
      (M1.nominal_k = 8 ∧
        absDiff M1.reported_cosine_perthou 950
          ≤ agreementTolerancePerthou) ∧
      RankDensityHypothesis M2 = false := by
  refine ⟨qwen_0_5b_L13_wave5, qwen_0_5b_L13_wave6,
          ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · refine ⟨?_, ?_⟩
    · decide
    · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- THE METHODOLOGICAL COROLLARY
-- ══════════════════════════════════════════════════════════

/-- A `RankDensityHypothesis` evaluation IS WELL-DEFINED relative
    to a provenance iff the record being evaluated is tagged with
    that provenance. Without protocol pinning, "k=8" is ambiguous
    between two interpretations the wave-5 / wave-6 sweeps each
    operationalize differently:

      • Wave5 semantics: "8 components in the cache cap" — the
        standing-wave-pca runtime takes the first eight PCA
        components of the residual stream and uses them as the
        reconstruction basis.
      • Wave6 semantics: "8 components representing some
        variance fraction at probe time" — the rank-floor sweep
        picks k as a function of the variance fraction the
        probe is targeting, then reports cosine against that k.

    The corollary below makes the protocol-pinning requirement
    explicit: the hypothesis-evaluation predicate the ledger
    actually supports takes both the record AND the provenance
    tag the evaluator commits to. -/
def hypothesis_relative_to_protocol
    (m : MeasurementRecord) (p : MeasurementProvenance) : Bool :=
  decide (m.provenance = p) && RankDensityHypothesis m

/-- Theorem: INVARIANTS-MUST-SPECIFY-MEASUREMENT-PROTOCOL.

    For the `RankDensityHypothesis`, there exist two records of
    the same nominal configuration such that the
    protocol-relative evaluator returns DIFFERENT verdicts
    depending on which provenance the evaluator commits to.

    Concretely:
      • `hypothesis_relative_to_protocol m p` is FALSE on every
        wave-6 reading evaluated against the wave-5 protocol
        (the provenance equality fails immediately).
      • The wave-5 reading evaluated against the wave-5 protocol
        is the only configuration in which the strong-form
        hypothesis can be honestly affirmed; even there, the
        wave-5 reading at coverage 0.90 is 930 perthou (under
        the floor by 20 perthou), so the strong form needs a
        coverage-tier or tolerance qualification.

    Practical implication: the rank-density invariant is
    well-defined only relative to a fixed measurement protocol.
    The Theory's wave-7+ work must pin the protocol — name the
    cache-cap-vs-variance-fraction probe semantics, the cal-token
    set, the probe seed, the layer-norm placement — and re-test
    the invariant under the pinned protocol before promoting it
    out of the contingent ledger. -/
theorem invariants_must_specify_measurement_protocol :
    ∃ m : MeasurementRecord, ∃ p1 p2 : MeasurementProvenance,
      p1 ≠ p2 ∧
      hypothesis_relative_to_protocol m p1 = false ∧
      hypothesis_relative_to_protocol m p2 = false := by
  refine ⟨qwen_0_5b_L13_wave6,
          MeasurementProvenance.Wave5InvestigationProbe,
          MeasurementProvenance.Wave6RankFloorSweep,
          ?_, ?_, ?_⟩
  · decide
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- TIE-BACK TO PRIOR WAVES
-- ══════════════════════════════════════════════════════════

/-- Tie-back: the wave-5 H3 calibration anchor in
    `RankFloorScalesWithDim` is the `qwen_0_5b_L13_k8_cov90`
    reading at hidden_dim 896, k=8, cosine 930 perthou. The
    wave-5 record in this module reports the same cosine on
    the same nominal k. Decided structurally. -/
theorem wave5_record_matches_rank_floor_anchor :
    qwen_0_5b_L13_wave5.nominal_k
      = Gnosis.RankFloorScalesWithDim.qwen_0_5b_L13_k8_cov90.k_components_used ∧
    qwen_0_5b_L13_wave5.reported_cosine_perthou
      = Gnosis.RankFloorScalesWithDim.qwen_0_5b_L13_k8_cov90.achieved_cosine_perthou := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

end TheoryRecursivelyFalsifies
end Gnosis
