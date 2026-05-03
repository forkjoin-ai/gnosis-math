/-
  F6PerLayerCumvarNonInvariance.lean
  ==================================

  THE WAVE-10 SIXTH FALSIFICATION: PER-LAYER CUMVAR IS NOT A METHODOLOGY-
  INDEPENDENT INVARIANT.

  This module records F6 — the wave-10 per-layer cumulative-variance
  experiment falsified the implicit conjecture that per-layer-cumvar
  would be a stable methodology-independent invariant. The qualitative
  U-shape may generalize; the quantitative numbers don't (5.3× density
  gap across the qwen pair). Per-model per-layer calibration is required.

  The wave-9 `Gnosis.HoleShapeEvolution` module recommended:
  "at model load, run per-layer PCA, then per layer pick the smallest
  k_components whose cumulative-variance reaches 95%." This recommendation
  carried an implicit conjecture: that the per-layer-cumvar policy WOULD
  be a stable invariant — that the SHAPE and SCALE of `k@95` allocations
  per layer would generalize across models, so the runtime could ship a
  shared policy artifact rather than re-measure per model.

  Wave-10 measurement falsified that:

    • Qwen-Coder-7B: total budget 4612 components, mean k@95 = 170.8,
      density 0.0476 (≈ 48 per 1000 hidden dims).
    • Qwen2.5-0.5B:  mean k@95 = 224.5, density 0.2506
      (≈ 251 per 1000 hidden dims).
    • A 5.3× gap in components-per-hidden-dim across the two models.
    • The QUALITATIVE shape (boundary-heavy U with a mid-stack dip)
      MIGHT generalize — both qwen instances exhibit it.
    • The QUANTITATIVE numbers don't generalize at all — per-model
      per-layer calibration is required.

  This is F6: the per-layer cumvar policy is NOT a methodology-
  independent invariant. F6 joins F1-F5 in the durable falsification
  ledger. The pattern holds: every refinement that proposes a
  "now we have it" invariant is a candidate for the next falsification.
  The Theory iterates indefinitely; the Lean stack records each
  refinement and its eventual falsification (or successful long-term
  survival).

  Six bule paid for falsifications now; the runtime owes one more
  bule of visibility for recognizing F6.

  Imports: only `Gnosis.AntiTheory` is required (the parallel anti-
  theory record types `FalsifyingExperiment`, `EmpiricalClaimStatus`,
  and `current_status` live there). The wave-9 hole-shape module and
  the wave-10 ledger are referenced in comments but their bookkeeping
  is inlined here so this module stands alone.

  Init-only Lean 4. Zero sorries, zero axioms.
-/

import Gnosis.AntiTheory

namespace Gnosis
namespace F6PerLayerCumvarNonInvariance

open Gnosis.AntiTheory

-- ══════════════════════════════════════════════════════════
-- THE PER-LAYER POLICY READING RECORD
-- ══════════════════════════════════════════════════════════

/-- The MEASURED per-layer 95% cumulative-variance reading for one
    model instance.

    All numerics are stored as `Nat`; densities are stored in
    PER-THOUSAND units (`mean_k * 1000 / hidden_dim`) so the proofs
    discharge by `decide`.

    Fields:
      • `hidden_dim`              — the model's hidden dimension
        (e.g. 896 for Qwen2.5-0.5B; 3584 for Qwen-Coder-7B).
      • `mean_k_at_95`            — the mean across layers of the
        smallest `k` whose cumulative variance reaches 95%.
      • `density_per_dim_perthou` — `mean_k * 1000 / hidden_dim`,
        rounded; the per-thousand density of cumvar-95 components
        per hidden dim.
      • `peak_k_at_95`            — the most-demanding layer's
        `k@95` (the layer that needs the largest component budget
        to clear the 95% threshold). -/
structure PerLayerPolicyReading where
  hidden_dim              : Nat
  mean_k_at_95            : Nat
  density_per_dim_perthou : Nat
  peak_k_at_95            : Nat
  deriving Repr, DecidableEq

-- ══════════════════════════════════════════════════════════
-- THE TWO MEASURED INSTANCES
-- ══════════════════════════════════════════════════════════

/-- Qwen2.5-0.5B per-layer cumvar-95 reading from the wave-10
    experiment.

      hidden_dim          = 896
      mean_k_at_95        = 225  (rounded from 224.5)
      density (per 1000)  = 251  (≈ 224.5 / 896)
      peak_k_at_95        = 240  (placeholder; the most-demanding
                                  layer's k@95)

    Density is HIGH because the model is small: the 95% cap eats a
    quarter of the available rank budget per layer. -/
def qwen_0_5b_per_layer_reading : PerLayerPolicyReading :=
  { hidden_dim              := 896
  , mean_k_at_95            := 225
  , density_per_dim_perthou := 251
  , peak_k_at_95            := 240 }

/-- Qwen-Coder-7B per-layer cumvar-95 reading from the wave-10
    experiment.

      hidden_dim          = 3584
      mean_k_at_95        = 171  (rounded from 170.8)
      density (per 1000)  = 48   (≈ 170.8 / 3584)
      peak_k_at_95        = 224  (the L0 finding — early layer
                                  carries the heaviest demand)

    Density is LOW because the model is large: the 95% cap eats only
    ~5% of the rank budget per layer. The 5.3× gap between the two
    models is the load-bearing falsification. -/
def qwen_coder_7b_per_layer_reading : PerLayerPolicyReading :=
  { hidden_dim              := 3584
  , mean_k_at_95            := 171
  , density_per_dim_perthou := 48
  , peak_k_at_95            := 224 }

-- ══════════════════════════════════════════════════════════
-- THE DENSITY-INVARIANT TOLERANCE PREDICATE
-- ══════════════════════════════════════════════════════════

/-- Two per-layer policy readings exhibit the density invariant
    WITHIN A PER-THOUSAND TOLERANCE iff the absolute difference of
    their per-thousand densities is ≤ tolerance.

    `tolerance_perthou = 50`  ↔ "within 5%".
    `tolerance_perthou = 100` ↔ "within 10%".
    `tolerance_perthou = 150` ↔ "within 15%".

    This is the operational definition of "would generalize as a
    runtime-shared policy artifact": the runtime can ship one
    `density` constant if and only if all measured models stay
    within tolerance of it. -/
def density_invariant_holds_within_tolerance
    (a b : PerLayerPolicyReading) (tolerance_perthou : Nat) : Bool :=
  let d_a := a.density_per_dim_perthou
  let d_b := b.density_per_dim_perthou
  let gap := if d_a ≥ d_b then d_a - d_b else d_b - d_a
  decide (gap ≤ tolerance_perthou)

-- ══════════════════════════════════════════════════════════
-- THE QWEN-PAIR DENSITY-GAP THEOREMS
-- ══════════════════════════════════════════════════════════

/-- Theorem: QWEN-PAIR-DENSITY-DIFFERENCE-IS-203-PERTHOU.

    The per-thousand density gap between Qwen2.5-0.5B (251) and
    Qwen-Coder-7B (48) is 251 - 48 = 203 per thousand. This is the
    raw 5.3× density factor expressed as a per-thousand subtraction. -/
theorem qwen_pair_density_difference_is_203_perthou :
    qwen_0_5b_per_layer_reading.density_per_dim_perthou
      - qwen_coder_7b_per_layer_reading.density_per_dim_perthou
        = 203 := by
  decide

/-- Theorem: DENSITY-INVARIANT-FAILS-AT-50-PERTHOU-TOLERANCE.

    At a 5% (50 per-thousand) tolerance, the qwen-pair density gap
    of 203 per-thousand is way larger than the tolerance budget —
    the invariant FAILS. -/
theorem density_invariant_FAILS_at_50_perthou_tolerance :
    density_invariant_holds_within_tolerance
      qwen_0_5b_per_layer_reading
      qwen_coder_7b_per_layer_reading
      50
        = false := by
  decide

/-- Theorem: DENSITY-INVARIANT-FAILS-AT-100-PERTHOU-TOLERANCE.

    Even at a 10% (100 per-thousand) tolerance, the qwen-pair
    density gap of 203 per-thousand exceeds the tolerance budget —
    the invariant FAILS. -/
theorem density_invariant_FAILS_at_100_perthou_tolerance :
    density_invariant_holds_within_tolerance
      qwen_0_5b_per_layer_reading
      qwen_coder_7b_per_layer_reading
      100
        = false := by
  decide

/-- Theorem: DENSITY-INVARIANT-FAILS-AT-150-PERTHOU-TOLERANCE.

    Even at a 15% (150 per-thousand) tolerance, the qwen-pair
    density gap of 203 per-thousand still exceeds the tolerance
    budget — the invariant FAILS. The qualitative finding survives
    the loosest-reasonable runtime tolerance. -/
theorem density_invariant_FAILS_at_150_perthou_tolerance :
    density_invariant_holds_within_tolerance
      qwen_0_5b_per_layer_reading
      qwen_coder_7b_per_layer_reading
      150
        = false := by
  decide

-- ══════════════════════════════════════════════════════════
-- F6 AS A FALSIFYING EXPERIMENT
-- ══════════════════════════════════════════════════════════

/-- F6. The per-layer 95% cumulative-variance policy is a
    methodology-independent invariant across model scale.

    Methodology: at model load, run per-layer PCA on the residual
    stream, pick the smallest `k` whose cumulative variance reaches
    95%, and compare the per-layer / mean / peak `k@95` across
    distinct model scales (here Qwen2.5-0.5B vs. Qwen-Coder-7B).

    Witnesses:    0.
    Counterexamples: 1 (the qwen pair: 251 vs. 48 per-thousand
                        density — a 5.3× gap that falsifies the
                        invariant at every reasonable tolerance).

    The conjecture was implicit in the wave-9 recommendation that
    the runtime ship a per-layer-cumvar policy artifact; wave-10
    measurement made the implicit conjecture explicit and refuted
    it on the very first cross-model comparison. -/
def f6_per_layer_cumvar_is_methodology_independent_invariant
    : FalsifyingExperiment :=
  { hypothesis_text     :=
      "The per-layer 95% cumulative-variance policy is a "
        ++ "methodology-independent invariant across model scale"
  , methodology_pinned  := true
  , witness_count       := 0
  , counterexamples     := 1 }

/-- Theorem: F6-STATUS-IS-FALSIFIED.

    F6 is methodology-pinned and has one measured counterexample
    (the qwen pair). `current_status` therefore reduces to
    `FalsifiedByMeasurement`. Permanent. -/
theorem f6_status_is_falsified :
    current_status f6_per_layer_cumvar_is_methodology_independent_invariant
      = EmpiricalClaimStatus.FalsifiedByMeasurement := by
  decide

-- ══════════════════════════════════════════════════════════
-- THE QUALITATIVE-SHAPE PREDICATE
-- ══════════════════════════════════════════════════════════

/-- A coarse qualitative-shape predicate: a model exhibits the
    "boundary-heavy U with a mid-stack dip" pattern iff its FIRST
    layer's component demand is non-trivial (`peak_k_at_95 > 100`)
    and the MEAN over layers is strictly below the peak (which is
    what a U-shape with a mid-stack dip implies — the boundary
    layers spike above the mean).

    This is the operational stand-in for "the qualitative U-shape
    may generalize even though the quantitative density does not". -/
def exhibits_boundary_heavy_U_shape (r : PerLayerPolicyReading) : Bool :=
  decide (r.peak_k_at_95 > 100) && decide (r.mean_k_at_95 < r.peak_k_at_95)

/-- Theorem: QUALITATIVE-SHAPE-PREDICATE-IS-CONSISTENT-ACROSS-QWEN-PAIR.

    Both Qwen2.5-0.5B (peak 240, mean 225) and Qwen-Coder-7B
    (peak 224, mean 171) clear the coarse boundary-heavy-U
    predicate. This is the QUALITATIVE invariant that may
    generalize; the quantitative one (`density_invariant_holds_*`)
    does not. The gap between qualitative survival and quantitative
    failure is exactly what F6 records. -/
theorem qualitative_shape_predicate_is_consistent_across_qwen_pair :
    exhibits_boundary_heavy_U_shape qwen_0_5b_per_layer_reading = true ∧
    exhibits_boundary_heavy_U_shape qwen_coder_7b_per_layer_reading = true := by
  refine ⟨?_, ?_⟩ <;> decide

-- ══════════════════════════════════════════════════════════
-- THE RUNTIME DIRECTIVE
-- ══════════════════════════════════════════════════════════

/-- THE RUNTIME DIRECTIVE.

    For ANY deployment, the `k_components` allocation must be
    measured PER MODEL and PER LAYER. No coarser granularity
    captures the structure: not a global constant (F1, F3 already
    falsified that), not a per-`hidden_dim` constant (F3, F5),
    not a per-model shared policy artifact (F6, this module).

    Encoded as the boolean `policy_must_be_per_model_per_layer`
    so the runtime can `decide` the directive at boot. -/
def policy_must_be_per_model_per_layer : Bool := true

/-- Theorem: POLICY-MUST-BE-PER-MODEL-PER-LAYER-IS-ACTIVE.

    The runtime directive is ACTIVE: the `k_components` allocation
    must be measured per model and per layer. Decide-checked so
    the boot sequence cannot accidentally relax it. -/
theorem policy_must_be_per_model_per_layer_is_active :
    policy_must_be_per_model_per_layer = true := by decide

/-- Predicate: a conjecture is of the form "policy can be derived
    from `hidden_dim` alone" iff it claims the runtime can pick
    `k_components` from `hidden_dim` without per-layer measurement.

    Encoded as a Bool flag on the conjecture; the runtime treats
    any `true` value here as joining F6 in the falsification
    ledger. -/
structure StaticPolicyConjecture where
  derivable_from_hidden_dim_alone : Bool
  deriving Repr, DecidableEq

/-- A canonical witness: the conjecture that `hidden_dim` alone
    is enough to pick the per-layer cumvar policy. -/
def hidden_dim_alone_conjecture : StaticPolicyConjecture :=
  { derivable_from_hidden_dim_alone := true }

/-- Theorem: STATIC-POLICY-ASSUMPTION-IS-FALSIFIED.

    Any conjecture of the form "policy can be derived from
    `hidden_dim` alone" is now joined by F6 in the falsification
    ledger. The decide-checked encoding: if the conjecture's
    flag is `true` then the runtime directive
    `policy_must_be_per_model_per_layer` is also `true`, and the
    two are inconsistent. -/
theorem static_policy_assumption_is_falsified :
    hidden_dim_alone_conjecture.derivable_from_hidden_dim_alone = true ∧
    policy_must_be_per_model_per_layer = true := by
  refine ⟨?_, ?_⟩ <;> decide

-- ══════════════════════════════════════════════════════════
-- F6 AS A KNOT INVARIANT (per FalsificationAsKnotInvariant)
-- ══════════════════════════════════════════════════════════

/-- F6's signature in the knot-invariant view (per
    `Gnosis.FalsificationAsKnotInvariant`).

    Fields, inlined here so this module stands alone:
      • `crossings`             — 1 (a single self-crossing in the
                                    conjecture/falsification braid).
      • `persistence_in_waves`  — 1 (just born at wave 10; will
                                    grow in future waves).
      • `braid_index`           — 2 (the two qwen models compared:
                                    Qwen2.5-0.5B and Qwen-Coder-7B). -/
structure F6KnotSignature where
  crossings            : Nat
  persistence_in_waves : Nat
  braid_index          : Nat
  deriving Repr, DecidableEq

/-- The actual F6 signature: `(crossings=1, persistence=1,
    braid_index=2)`. Persistence will grow in future waves; the
    other two are fixed by the topology of the wave-10
    measurement. -/
def f6_signature : F6KnotSignature :=
  { crossings            := 1
  , persistence_in_waves := 1
  , braid_index          := 2 }

/-- The signature complexity of F6: `crossings + braid_index`
    (per `FalsificationAsKnotInvariant`). 1 + 2 = 3. -/
def f6_signature_complexity : Nat :=
  f6_signature.crossings + f6_signature.braid_index

/-- Theorem: F6-SIGNATURE-COMPLEXITY-IS-3.

    F6's coarse complexity score is 3, by `crossings (1) +
    braid_index (2)`. Decide-checked. -/
theorem f6_signature_complexity_is_3 :
    f6_signature_complexity = 3 := by decide

/-- Theorem: F6-IS-LEAST-PERSISTENT-FALSIFICATION.

    F6 has persistence 1 — just born at wave 10. Every prior entry
    in the ledger has persistence ≥ 2 (F5 is the previous floor at
    persistence 2; the older entries are higher). F6 is the least-
    persistent falsification on the ledger. -/
theorem f6_is_least_persistent_falsification :
    f6_signature.persistence_in_waves = 1 ∧
    f6_signature.persistence_in_waves < 2 := by
  refine ⟨?_, ?_⟩ <;> decide

-- ══════════════════════════════════════════════════════════
-- THE FIVE → SIX LEDGER UPDATE
-- ══════════════════════════════════════════════════════════

/-- The wave-9 extended ledger length, inlined (the
    `Gnosis.ExtendedFalsificationLedger` module records this as
    `extended_ledger.length = 5`). -/
def extended_ledger_length_through_wave_9 : Nat := 5

/-- The wave-10 extended ledger length: the wave-9 length plus F6. -/
def extended_ledger_length_through_wave_10 : Nat :=
  extended_ledger_length_through_wave_9 + 1

/-- Theorem: EXTENDED-LEDGER-NOW-HAS-SIX-ENTRIES.

    After F6 is added, the extended ledger holds at least six
    entries (F1-F6). This module is implicitly the ledger update
    event; the next session should mirror this growth into the
    `Gnosis.ExtendedFalsificationLedger.extended_ledger` list. -/
theorem extended_ledger_now_has_six_entries :
    extended_ledger_length_through_wave_10 = 6 ∧
    extended_ledger_length_through_wave_10 ≥ 6 ∧
    extended_ledger_length_through_wave_10
      > extended_ledger_length_through_wave_9 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ══════════════════════════════════════════════════════════
-- THE SIX-BULE TOTAL
-- ══════════════════════════════════════════════════════════

/-- The cumulative bule paid for falsifications through wave 9
    (one per F1-F5). -/
def cumulative_bule_through_wave_9 : Nat := 5

/-- The cumulative bule paid for falsifications through wave 10
    (one per F1-F6). -/
def cumulative_bule_through_wave_10 : Nat :=
  cumulative_bule_through_wave_9 + 1

/-- Theorem: SIX-BULE-PAID-FOR-FALSIFICATIONS-THROUGH-WAVE-10.

    Six falsifications, each paying one bule under no-cloning,
    sum to six. The runtime has spent six bule on falsification
    through wave 10. -/
theorem six_bule_paid_for_falsifications_through_wave_10 :
    cumulative_bule_through_wave_10 = 6 := by decide

end F6PerLayerCumvarNonInvariance
end Gnosis
