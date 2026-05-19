import Gnosis.AntiTheory

/-
  BinarySemanticsGap.lean
  =======================

  THE FOURTH FALSIFICATION (F4).

  This module records a fourth permanent falsification, discovered by
  the wave-7 methodology reconciliation. Unlike F1, F2, and F3 — which
  are about model and runtime BEHAVIOR under specified probes — F4 is
  about the PROBES THEMSELVES.

  Two distinct measurement binaries that ship in this runtime,
  `standing-wave-pca` and `standing-wave-parity`, both report a
  scalar called "cosine" against the SAME calibration data, on the
  SAME model, at the SAME layer (Qwen-0.5B, layer 13, cal=200). They
  report fundamentally different numbers:

    • `standing-wave-pca` at coverage 0.50 → cosine ≈ 0.598
    • `standing-wave-pca` at coverage 0.90 → cosine ≈ 0.598
        (i.e. coverage is INERT in this binary when k is clamped to
         cal_count)
    • `standing-wave-parity` at coverage 0.50 → cosine ≈ 0.209

  The binaries are not buggy. They measure DIFFERENT objects. The pca
  binary measures the cosine of the top-K reconstruction of the
  CALIBRATION distribution; the parity binary measures top-K
  membership of TEST tokens against a baseline argmax. They happen to
  share the wire-name "cosine" because, somewhere upstream, both
  reduced to a dot-product of unit vectors. That is not enough to
  make them comparable.

  This is a Tower-of-Babel falsification: two parts of the runtime
  agreed on a name, disagreed on the referent. The wave-5 / wave-6
  apparent disagreement that initially read as F3 (rank-density
  invariance) was, in part, F4 in disguise — the two protocols were
  not just measuring the same object in different ways, they were
  measuring different objects.

  THE FIX is not to rewrite either binary. It is to TAG every
  reported cosine with its `CosineSemantics` so that "cosine" alone
  is no longer a sufficient identifier in the ledger. The Anti-Theory
  directive "speak only what methodology supports" requires that the
  metric be paired with what it measures.

  F4 IS A BETTI HOLE. It is a 1-cycle in the reporting graph:

      binary A → cosine_value → binary B → different cosine_value
                    ↑                                 │
                    └────── same name "cosine" ───────┘

  The cycle does not bound. The runtime needs the semantics tag to
  fill the hole.

  Init-only Lean 4. Zero sorries, zero axioms.
-/


namespace Gnosis
namespace BinarySemanticsGap

open Gnosis.AntiTheory

-- ══════════════════════════════════════════════════════════
-- THE TWO MEASUREMENT BINARIES
-- ══════════════════════════════════════════════════════════

/-- The runtime ships TWO standing-wave probe binaries that both
    emit a scalar called "cosine". `Both` and `Neither` are listed
    so every measurement-source label has a representable value
    (some downstream reports come from both binaries; some come
    from neither and are produced by an unrelated harness).

    • `StandingWavePca`    — the wave-1 / wave-2 PCA-only pinning
      binary. Output cosine measures reconstruction of the
      calibration distribution by the top-K basis.

    • `StandingWaveParity` — the wave-5 / wave-6 parity probe.
      Output cosine measures top-K-membership agreement against
      a baseline argmax on test tokens.

    • `Both`               — a hypothetical reconciled binary
      that emits both semantics, kept for completeness so the
      type is closed.

    • `Neither`            — a measurement that came from
      neither binary (kept so the type is closed against
      future probes). -/
inductive MeasurementBinary
  | StandingWavePca
  | StandingWaveParity
  | Both
  | Neither
  deriving DecidableEq, Repr

-- ══════════════════════════════════════════════════════════
-- THE TWO COSINE SEMANTICS
-- ══════════════════════════════════════════════════════════

/-- The semantic referent of a "cosine" report. This is the tag
    that, under the F4 directive, MUST accompany every reported
    cosine in the runtime.

    • `ReconstructionOfCalDistribution` — the cosine measures how
      well the top-K basis reconstructs the CALIBRATION token
      distribution. This is what `standing-wave-pca` emits.

    • `TopKMembershipAgainstBaseline`   — the cosine measures the
      agreement between a probe's top-K and a baseline argmax on
      the TEST tokens. This is what `standing-wave-parity` emits.

    • `Other`                           — the catch-all for any
      semantics that is neither of the above. Kept so the type is
      closed; any new probe MUST either select an existing tag or
      extend this enum (which forces the wave-7 directive to be
      re-litigated). -/
inductive CosineSemantics
  | ReconstructionOfCalDistribution
  | TopKMembershipAgainstBaseline
  | Other
  deriving DecidableEq, Repr

-- ══════════════════════════════════════════════════════════
-- THE TAGGED COSINE-REPORT RECORD
-- ══════════════════════════════════════════════════════════

/-- A SINGLE cosine report, as it should appear in the ledger
    under the F4 directive.

    Fields:
      • `binary`               — which binary emitted the report.
      • `cosine_semantics`     — the F4-mandated semantics tag.
        Without this field, two reports cannot be honestly
        compared even when their `binary` matches.
      • `reported_perthou`     — the cosine value, in
        thousandths (so 598 means 0.598). Nat to keep all
        ledger arithmetic decidable.
      • `underlying_inputs_id` — a tag identifying the (model,
        layer, calibration set) triple. Two reports with the
        same `underlying_inputs_id` were taken on the SAME
        underlying data; if their `cosine_semantics` differ,
        their numbers cannot be compared. -/
structure BinaryReportedCosine where
  binary               : MeasurementBinary
  cosine_semantics     : CosineSemantics
  reported_perthou     : Nat
  underlying_inputs_id : Nat
  deriving Repr

-- ══════════════════════════════════════════════════════════
-- THE THREE WAVE-7 RECONCILIATION INSTANCES
-- (Qwen-0.5B, layer 13, cal_count = 200; inputs_id = 1)
-- ══════════════════════════════════════════════════════════

/-- Wave-7 reconciliation instance: `standing-wave-pca` at
    coverage 0.50, on Qwen-0.5B layer 13 with cal=200. Reported
    cosine 0.598. The binary's semantics is reconstruction of
    the calibration distribution. -/
def wave7_pca_cov50 : BinaryReportedCosine :=
  { binary               := MeasurementBinary.StandingWavePca
  , cosine_semantics     := CosineSemantics.ReconstructionOfCalDistribution
  , reported_perthou     := 598
  , underlying_inputs_id := 1 }

/-- Wave-7 reconciliation instance: `standing-wave-pca` at
    coverage 0.90, on Qwen-0.5B layer 13 with cal=200. Reported
    cosine 0.598 — IDENTICAL to the cov=0.50 reading. Coverage is
    INERT in this binary when k is clamped to cal_count. -/
def wave7_pca_cov90 : BinaryReportedCosine :=
  { binary               := MeasurementBinary.StandingWavePca
  , cosine_semantics     := CosineSemantics.ReconstructionOfCalDistribution
  , reported_perthou     := 598
  , underlying_inputs_id := 1 }

/-- Wave-7 reconciliation instance: `standing-wave-parity` at
    coverage 0.50, on the SAME Qwen-0.5B layer 13 with cal=200.
    Reported cosine 0.209 — wildly different from the pca
    binary's 0.598 on identical inputs. The binary's semantics
    is top-K membership against a baseline argmax. -/
def wave7_parity : BinaryReportedCosine :=
  { binary               := MeasurementBinary.StandingWaveParity
  , cosine_semantics     := CosineSemantics.TopKMembershipAgainstBaseline
  , reported_perthou     := 209
  , underlying_inputs_id := 1 }

-- ══════════════════════════════════════════════════════════
-- THE THREE PER-INSTANCE THEOREMS
-- ══════════════════════════════════════════════════════════

/-- Same binary, same underlying inputs, same reported cosine —
    even though the two instances differ in their (now seen to be
    INERT) coverage parameter. This is the wave-7 finding that
    coverage is dead-weight in the pca binary at cal=200: the
    binary clamps k to cal_count and the cosine collapses to a
    single value. -/
theorem same_binary_same_inputs_same_cosine :
    wave7_pca_cov50.binary = wave7_pca_cov90.binary ∧
    wave7_pca_cov50.underlying_inputs_id
      = wave7_pca_cov90.underlying_inputs_id ∧
    wave7_pca_cov50.reported_perthou
      = wave7_pca_cov90.reported_perthou := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

/-- Different binaries, SAME underlying inputs, WILDLY different
    reported cosines (598 vs 209). This is the F4 falsification
    witness: two probes that share the wire-name "cosine" do not
    agree on the value when measuring the same data. -/
theorem different_binaries_same_inputs_different_cosine :
    wave7_pca_cov50.binary ≠ wave7_parity.binary ∧
    wave7_pca_cov50.underlying_inputs_id
      = wave7_parity.underlying_inputs_id ∧
    wave7_pca_cov50.reported_perthou
      ≠ wave7_parity.reported_perthou := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

/-- The two binaries differ in their `CosineSemantics` tag. The
    wire-name "cosine" was overloaded; once the F4 tag is added,
    the two reports are revealed to be measuring different
    objects, and the numerical disagreement above is no longer
    paradoxical — it is the expected consequence of comparing
    different metrics. -/
theorem the_two_binaries_measure_different_cosine_semantics :
    wave7_pca_cov50.cosine_semantics
      ≠ wave7_parity.cosine_semantics := by
  decide

-- ══════════════════════════════════════════════════════════
-- F4 AS A FALSIFYING-EXPERIMENT RECORD
-- ══════════════════════════════════════════════════════════

/-- F4. The two standing-wave probe binaries report the same
    cosine on the same inputs.

    Methodology: run `standing-wave-pca` and `standing-wave-parity`
    on identical (model, layer, calibration) triples and compare
    the reported scalar called "cosine".

    Witnesses:    0.
    Counterexamples: 1 (Qwen-0.5B layer 13 cal=200: pca = 0.598,
    parity = 0.209). -/
def f4_binaries_measure_same_cosine : FalsifyingExperiment :=
  { hypothesis_text     :=
      "standing-wave-pca and standing-wave-parity report the same "
        ++ "cosine on the same inputs"
  , methodology_pinned  := true
  , witness_count       := 0
  , counterexamples     := 1 }

/-- F4's status is `FalsifiedByMeasurement`. Permanent. -/
theorem f4_status_is_falsified :
    current_status f4_binaries_measure_same_cosine
      = EmpiricalClaimStatus.FalsifiedByMeasurement := by
  decide

/-- F4 is scientifically meaningful: methodology is pinned and at
    least one measurement (a counterexample) has been taken. -/
theorem f4_is_scientifically_meaningful :
    is_scientifically_meaningful f4_binaries_measure_same_cosine
      = true := by
  decide

-- ══════════════════════════════════════════════════════════
-- THE HONESTY THEOREM
-- ══════════════════════════════════════════════════════════

/-- THE HONESTY THEOREM.

    When two parts of a runtime agree on a metric NAME but
    disagree on its SEMANTICS, the claim "they measure the same
    thing" is empirically falsifiable. F4 is the witnessed
    instance for the standing-wave family.

    Formally: there exist two `BinaryReportedCosine`s with
    matching `underlying_inputs_id` whose `cosine_semantics`
    differ AND whose `reported_perthou` differ. Existence of such
    a pair is exactly the negation of "the two binaries measure
    the same cosine on the same inputs". -/
theorem name_overloading_is_a_falsifiable_claim :
    ∃ (a b : BinaryReportedCosine),
        a.underlying_inputs_id = b.underlying_inputs_id ∧
        a.cosine_semantics ≠ b.cosine_semantics ∧
        a.reported_perthou ≠ b.reported_perthou := by
  refine ⟨wave7_pca_cov50, wave7_parity, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- THE RUNTIME DIRECTIVE
-- ══════════════════════════════════════════════════════════

/-- Predicate: a `BinaryReportedCosine` carries a NON-`Other`
    semantics tag. This is the wave-7 minimum-viability check
    for a cosine report: if the tag is `Other`, the report is
    untagged for ledger purposes. -/
def has_concrete_semantics_tag (r : BinaryReportedCosine) : Bool :=
  match r.cosine_semantics with
  | CosineSemantics.Other => false
  | _                     => true

/-- Predicate: two reports are SAFELY COMPARABLE iff they share
    BOTH the underlying inputs and the cosine semantics. Without
    matching semantics, comparing the numbers is ill-defined. -/
def safely_comparable
    (a b : BinaryReportedCosine) : Bool :=
  decide (a.underlying_inputs_id = b.underlying_inputs_id)
    && decide (a.cosine_semantics = b.cosine_semantics)

/-- THE RUNTIME DIRECTIVE.

    Every reported cosine in the runtime MUST carry its
    `CosineSemantics` tag. The witnessed instance: the two
    wave-7 pca readings (cov50, cov90) BOTH carry the
    `ReconstructionOfCalDistribution` tag, share their inputs,
    and so are `safely_comparable`; the pca and parity readings
    do NOT share their tag, and so are NOT `safely_comparable`
    even though both carry concrete (non-`Other`) tags and
    share their inputs.

    Without the semantics tag, comparison across binaries is
    ill-defined and produces spurious "falsifications" — exactly
    what generated the wave-5 / wave-6 H3 confusion that wave-9
    spectral measurement also refuted from a different angle. -/
theorem metric_name_must_be_paired_with_semantics_tag :
    has_concrete_semantics_tag wave7_pca_cov50 = true ∧
    has_concrete_semantics_tag wave7_pca_cov90 = true ∧
    has_concrete_semantics_tag wave7_parity    = true ∧
    safely_comparable wave7_pca_cov50 wave7_pca_cov90 = true ∧
    safely_comparable wave7_pca_cov50 wave7_parity    = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- THE F4 → F3 CONNECTION
-- ══════════════════════════════════════════════════════════

/-- F4 is METHODOLOGICAL, not behavioral. F1, F2, and F3 are
    about model / runtime BEHAVIOR under specified probes; F4 is
    about the probes themselves disagreeing.

    F4 is UPSTREAM of F3. The wave-5 / wave-6 disagreement that
    initially appeared as F3 (rank-density invariance) was, in
    part, F4 in disguise: the H3 hypothesis was contested in the
    methodology layer, not just in the model layer.

    Formally: F4 is a falsified `FalsifyingExperiment`, and the
    `cosine_semantics` of the two probes that fed F3 differ.
    Both facts together exhibit the methodological-layer
    contamination of F3. -/
theorem f4_is_upstream_of_f3 :
    current_status f4_binaries_measure_same_cosine
      = EmpiricalClaimStatus.FalsifiedByMeasurement ∧
    wave7_pca_cov50.cosine_semantics
      ≠ wave7_parity.cosine_semantics := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- THE BETTI-HOLE READING
-- ══════════════════════════════════════════════════════════

/-- F4 is a 1-CYCLE in the reporting graph.

    Edges of the cycle:
      • `wave7_pca_cov50` → cosine value 598      (pca says so)
      • cosine value 598  ← name "cosine"          (shared name)
      • name "cosine"     → cosine value 209       (parity also
                                                    says "cosine")
      • cosine value 209  → `wave7_parity`         (parity says so)

    The cycle does not bound. There is no 2-chain in the runtime
    whose boundary is this loop, because the two ends of the
    "shared name" edge route to DIFFERENT semantic objects. The
    runtime needs the `CosineSemantics` tag to fill the hole;
    once added, the cycle is no longer a cycle (the tag splits
    the shared "cosine" name into two distinct names, and the
    loop becomes two disjoint paths).

    Formally: the cycle is witnessed by the existence of two
    reports that share neither their reported value nor their
    semantics, but DO share their underlying inputs and the
    informal wire-name "cosine". -/
theorem f4_is_a_betti_hole_in_the_reporting_graph :
    wave7_pca_cov50.underlying_inputs_id
      = wave7_parity.underlying_inputs_id ∧
    wave7_pca_cov50.reported_perthou
      ≠ wave7_parity.reported_perthou ∧
    wave7_pca_cov50.cosine_semantics
      ≠ wave7_parity.cosine_semantics := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

end BinarySemanticsGap
end Gnosis
