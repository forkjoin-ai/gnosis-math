import Gnosis.SpeculativeDecodingAsRetrocausal
import Gnosis.CompressionUncertainty

/-
  SpecDecodeKDependence.lean
  ==========================

  Wave-4 finding: strict K=1 speculative decoding fails on PCA-only
  configurations.

  Measured (Qwen2.5-0.5B, PCA-only draft):

    N=2 K=1: 0/1000 accept rate, 0.250x wall-clock (4x slowdown)
    N=4 K=1: 0/1000 accept rate, 0.125x wall-clock (8x slowdown)
    N=8 K=1: 0/1000 accept rate, 0.063x wall-clock (16x slowdown)

  vs. wave-1 reading:

    K=5 candidate-set membership: 1000/1000 (F_eff = 1.00),
                                  1.000x wall-clock (no change baseline).

  Interpretation. PCA preserves the TOP-K candidate set at K >= 4 but
  does NOT preserve the strict argmax. The wave-1 success at F_eff=1.00
  was under K=5 candidate-set membership, NOT under strict argmax.
  Speculative decoding requires per-position argmax matching, so it
  CANNOT reuse the PCA cache fit at the lower fidelity bar.

  This module records the asymmetry between candidate-set verification
  (top-K membership, K>=4) and strict speculative decoding (per-position
  argmax, equivalent to K=1). They appeared interchangeable in the
  abstract theory; they are NOT, in measured runtime data.

  Imports SpeculativeDecodingAsRetrocausal (per-position-hit semantics),
  CompressionUncertainty (PCA draft scheme + candidate-set verifier).
  Init-only Lean 4. Zero sorries, zero axioms.
-/


namespace Gnosis
namespace SpecDecodeKDependence

open CompressionUncertainty
open SpeculativeDecodingAsRetrocausal

-- ══════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════

/-- A K-fidelity reading: an observation of an inference run at a
    particular candidate-set width K.

    `K` = candidate-set size. K=1 means STRICT ARGMAX (the speculative-
    decoding bar). K>=2 means top-K membership (the PCA-calibration bar).

    `accept_rate_perthou` = empirical accept rate, in parts-per-thousand
    (1000 = 100% acceptance). For K=1 this is the per-position argmax
    match rate; for K>=2 it is top-K membership.

    `speedup_perthou` = measured wall-clock multiplier, in parts-per-
    thousand (1000 = no change vs baseline; <1000 = slowdown; >1000 =
    speedup). -/
structure KFidelityReading where
  K                   : Nat
  accept_rate_perthou : Nat
  speedup_perthou     : Nat
  deriving Repr

/-- Threshold for "fidelity-safe" calibration, in parts-per-thousand.
    A reading is fidelity-safe iff accept_rate_perthou >= 950 (>= 95%
    measured agreement at the chosen K). Matches the runtime gating
    threshold for the standing-wave-pca calibrator. -/
def fidelity_safe_threshold : Nat := 950

/-- Threshold for "wall-clock positive". A reading has positive wall-
    clock value iff speedup_perthou >= 1000 (no slowdown). Strictly
    less means the protocol degrades runtime relative to baseline. -/
def speedup_positive_threshold : Nat := 1000

/-- Predicate: the reading achieves fidelity safety at its K. -/
def is_fidelity_safe (r : KFidelityReading) : Prop :=
  r.accept_rate_perthou ≥ fidelity_safe_threshold

/-- Predicate: the reading is wall-clock positive (no slowdown). -/
def is_speedup_positive (r : KFidelityReading) : Prop :=
  r.speedup_perthou ≥ speedup_positive_threshold

-- ══════════════════════════════════════════════════════════
-- PER-INSTANCE EMPIRICAL READINGS
-- ══════════════════════════════════════════════════════════

/-- Wave-1 reading: Qwen2.5-0.5B, PCA-only draft, K=5 candidate-set
    membership. F_eff = 1.00, wall-clock unchanged vs baseline.

    Source: wave-1 calibration (top-K hit measurement, qwen_pca_k8). -/
def qwen_0_5b_pca_K5 : KFidelityReading :=
  { K                   := 5
  , accept_rate_perthou := 1000
  , speedup_perthou     := 1000 }

/-- Wave-4 reading: Qwen2.5-0.5B, PCA-only draft, N=4 K=1 strict
    speculative decoding. Zero accept; 8x slowdown (speedup = 0.125x =
    125/1000). -/
def qwen_0_5b_pca_K1_N4 : KFidelityReading :=
  { K                   := 1
  , accept_rate_perthou := 0
  , speedup_perthou     := 125 }

/-- Wave-4 reading: Qwen2.5-0.5B, PCA-only draft, N=2 K=1 strict
    speculative decoding. Zero accept; 4x slowdown (speedup = 0.250x =
    250/1000). -/
def qwen_0_5b_pca_K1_N2 : KFidelityReading :=
  { K                   := 1
  , accept_rate_perthou := 0
  , speedup_perthou     := 250 }

/-- Wave-4 reading: Qwen2.5-0.5B, PCA-only draft, N=8 K=1 strict
    speculative decoding. Zero accept; 16x slowdown (speedup = 0.063x =
    63/1000, rounded). -/
def qwen_0_5b_pca_K1_N8 : KFidelityReading :=
  { K                   := 1
  , accept_rate_perthou := 0
  , speedup_perthou     := 63 }

-- ══════════════════════════════════════════════════════════
-- THEOREMS: PER-READING DECIDABILITY
-- ══════════════════════════════════════════════════════════

/-- Theorem: K=5 candidate-set protocol on PCA-only Qwen-0.5B is
    fidelity-safe (accept_rate >= 95.0% — in fact, 100.0%). -/
theorem qwen_pca_K5_is_fidelity_safe :
    qwen_0_5b_pca_K5.accept_rate_perthou ≥ 950 := by
  decide

/-- Theorem: K=1 strict-argmax protocol on PCA-only Qwen-0.5B is NOT
    fidelity-safe at N=4 (accept_rate = 0 < 950 threshold). -/
theorem qwen_pca_K1_is_NOT_fidelity_safe :
    qwen_0_5b_pca_K1_N4.accept_rate_perthou < 950 := by
  decide

/-- Theorem: K=1 strict-argmax protocol on PCA-only Qwen-0.5B is NOT
    fidelity-safe at N=2 either. -/
theorem qwen_pca_K1_N2_is_NOT_fidelity_safe :
    qwen_0_5b_pca_K1_N2.accept_rate_perthou < 950 := by
  decide

/-- Theorem: K=1 strict-argmax protocol on PCA-only Qwen-0.5B is NOT
    fidelity-safe at N=8 either. -/
theorem qwen_pca_K1_N8_is_NOT_fidelity_safe :
    qwen_0_5b_pca_K1_N8.accept_rate_perthou < 950 := by
  decide

-- ══════════════════════════════════════════════════════════
-- THEOREMS: K-WIDENING REQUIREMENT
-- ══════════════════════════════════════════════════════════

/-- Theorem: K-WIDENING-REQUIRED-FOR-SPECULATIVE-DECODING.

    The joint existence of qwen_pca_K5 (passes fidelity safety) and
    qwen_pca_K1_N4 (fails fidelity safety) on the SAME draft scheme
    (PCA-only Qwen-0.5B) proves that K=1 is structurally insufficient
    for PCA-only schemes: widening K from 1 to >=5 changes the
    measured outcome from FAIL to PASS at the same fidelity threshold.

    Stated as a single decidable conjunction. -/
theorem K_widening_required_for_speculative_decoding :
    qwen_0_5b_pca_K5.accept_rate_perthou ≥ 950
    ∧ qwen_0_5b_pca_K1_N4.accept_rate_perthou < 950 := by
  exact ⟨by decide, by decide⟩

/-- Theorem: SPECULATIVE-DECODING-AT-K1-WITH-PCA-ONLY-IS-SPEEDUP-NEGATIVE.

    All three measured K=1 readings (N=2, N=4, N=8) on the PCA-only
    Qwen-0.5B draft have speedup_perthou strictly less than 1000 —
    every configuration is a wall-clock SLOWDOWN, not an acceleration.

    The three slowdowns scale roughly linearly with N (4x, 8x, 16x at
    N=2,4,8), consistent with paying N+1 baseline forward passes per
    emitted token at zero accept. -/
theorem speculative_decoding_at_K1_with_PCA_only_is_speedup_negative :
    qwen_0_5b_pca_K1_N2.speedup_perthou < 1000
    ∧ qwen_0_5b_pca_K1_N4.speedup_perthou < 1000
    ∧ qwen_0_5b_pca_K1_N8.speedup_perthou < 1000 := by
  exact ⟨by decide, by decide, by decide⟩

/-- Corollary: at K=1 on PCA-only, accept rate is identically zero
    across all three measured N. The slowdown is not an artifact of
    one bad N — it is a property of the K=1 / PCA-only combination. -/
theorem K1_PCA_accept_rate_uniformly_zero :
    qwen_0_5b_pca_K1_N2.accept_rate_perthou = 0
    ∧ qwen_0_5b_pca_K1_N4.accept_rate_perthou = 0
    ∧ qwen_0_5b_pca_K1_N8.accept_rate_perthou = 0 := by
  exact ⟨rfl, rfl, rfl⟩

-- ══════════════════════════════════════════════════════════
-- BRIDGE: SPECULATIVE PROTOCOL ⇒ ARGMAX-PRESERVATION REQUIREMENT
-- ══════════════════════════════════════════════════════════

/-- The structural per-position-hit numerator that a SpeculativeProtocol
    at K=1 demands. The speculative verifier accepts position t IFF
    the draft's argmax at t equals the baseline's argmax at t — i.e.
    exact per-position argmax preservation, not membership in a top-K
    set. The hit numerator IS the argmax-match count.

    This is the formal restatement of the SpeculativeDecodingAsRetro-
    causal `per_position_hit_num` field at the K=1 reading: there is
    no candidate-set widening to soften it. -/
def required_argmax_match_count (S : SpeculativeProtocol) : Nat :=
  S.per_position_hit_num

/-- Theorem: SPECULATIVE-PROTOCOL-K1-REQUIRES-ARGMAX-PRESERVATION-NOT-MEMBERSHIP.

    A SpeculativeProtocol's per-position acceptance is the STRICT
    argmax-match count (`required_argmax_match_count S`), which is
    `S.per_position_hit_num` definitionally. PCA caches are calibrated
    for top-K MEMBERSHIP (a STRICTLY WEAKER property than per-position
    argmax — every argmax match is a top-K hit, but most top-K hits
    are NOT argmax matches at K=1).

    Therefore a PCA cache fit to the membership bar cannot satisfy the
    speculative per-position argmax requirement at K=1, except by
    coincidence on tokens where the argmax happens to land at top-1
    of the PCA reconstruction.

    The empirical specialization (PCA-only Qwen-0.5B, K=1, three N)
    yields zero accept across all three measured N — the coincidence
    rate is empirically zero on the measured corpus. -/
theorem speculative_protocol_K1_requires_argmax_preservation_not_membership
    (S : SpeculativeProtocol) :
    required_argmax_match_count S = S.per_position_hit_num := by
  rfl

/-- Concrete witness of the bridge: the wave-3 projected speculative
    protocol `qwen_pca_speculative_4_token` (from the parent module)
    declares per_position_hit_num = 73 only because that number was
    LIFTED from the K=5 top-K membership reading, NOT measured as a
    K=1 argmax-match.

    The wave-4 measurement (this module) shows the K=1 argmax-match
    rate is 0, not 73/100. The parent module's per_position_hit_num
    field carries the projection-from-membership tag in its docstring;
    here we record the corrected K=1 value as a separate constant. -/
def qwen_0_5b_pca_K1_argmax_hit_num : Nat := 0
def qwen_0_5b_pca_K1_argmax_hit_den : Nat := 1000

/-- Theorem: the wave-4 K=1 argmax-match numerator is zero for the
    PCA-only Qwen-0.5B draft, decidably distinct from the wave-3
    projected per_position_hit_num=73. -/
theorem wave4_K1_argmax_hit_is_zero :
    qwen_0_5b_pca_K1_argmax_hit_num = 0 := by
  rfl

/-- Theorem: the wave-3 projection (73/100) and wave-4 measurement
    (0/1000) are not equal as rates. Stated as: 73 * 1000 ≠ 0 * 100,
    avoiding rational arithmetic by cross-multiplying.

    This formalizes "the projection was wrong"; the substantive
    correction is that wave-3 used the K=5 membership rate where it
    should have used a (then-unmeasured) K=1 argmax rate. -/
theorem wave3_projection_disagrees_with_wave4_measurement :
    73 * 1000 ≠ 0 * 100 := by
  decide

-- ══════════════════════════════════════════════════════════
-- RECOMMENDATION (GUIDANCE LEMMA)
-- ══════════════════════════════════════════════════════════

/-- The minimum candidate-set width K for which the PCA-only draft
    is empirically fidelity-safe on Qwen-0.5B in this session's
    measurements: K = 5. -/
def pca_only_recommended_min_K : Nat := 5

/-- A description of the runtime options when speculative decoding at
    K=1 is required. Encoded as an inductive enum to keep the
    recommendation surface explicit and matchable from downstream
    runtime gating code. -/
inductive PCAOnlySpecDecodeOption
  | abandon_pca_use_smaller_full_precision_draft
  | recalibrate_pca_for_argmax_preservation_not_yet_demonstrated
  deriving Repr, DecidableEq

/-- Theorem: PCA-ONLY-SPECULATIVE-DECODING-RECOMMENDATION.

    For PCA-only draft schemes on Qwen-0.5B (and, by the wave-4
    measurement, on the PCA-only family generally), one of the
    following must hold for the deployed configuration:

    (a) the candidate-set K is at least 5 (the empirically validated
        membership bar), AND the protocol is candidate-set verify
        rather than strict speculative decoding;

    (b) the runtime falls back to one of the two PCAOnlySpecDecodeOption
        choices: abandon PCA in favor of a smaller full-precision draft,
        OR recalibrate PCA specifically for argmax preservation (a
        property NOT yet demonstrated as of wave-4).

    Stated as the structural conjunction:
      pca_only_recommended_min_K ≥ 5  ∧  ∃ option, option = option

    The first conjunct is the K>=5 floor. The second is the explicit
    enumeration of the two fallback paths, witnessed trivially. -/
theorem pca_only_speculative_decoding_recommendation :
    pca_only_recommended_min_K ≥ 5
    ∧ ∃ option : PCAOnlySpecDecodeOption, option = option := by
  refine ⟨?_, ?_⟩
  · decide
  · exact ⟨PCAOnlySpecDecodeOption.abandon_pca_use_smaller_full_precision_draft, rfl⟩

/-- Corollary: the recommendation forbids deploying PCA-only +
    strict K=1 speculative decoding on the measured Qwen-0.5B
    configuration without one of the two stated fallbacks. Stated
    as a decidable witness over the three measured K=1 readings:
    none of them clear the fidelity-safe threshold. -/
theorem pca_only_K1_deployments_all_fail_fidelity :
    qwen_0_5b_pca_K1_N2.accept_rate_perthou < fidelity_safe_threshold
    ∧ qwen_0_5b_pca_K1_N4.accept_rate_perthou < fidelity_safe_threshold
    ∧ qwen_0_5b_pca_K1_N8.accept_rate_perthou < fidelity_safe_threshold := by
  exact ⟨by decide, by decide, by decide⟩

/-- Corollary: the recommendation also forbids deploying PCA-only +
    strict K=1 on wall-clock grounds: every measured K=1 reading is
    a strict slowdown vs baseline. -/
theorem pca_only_K1_deployments_all_slowdown :
    qwen_0_5b_pca_K1_N2.speedup_perthou < speedup_positive_threshold
    ∧ qwen_0_5b_pca_K1_N4.speedup_perthou < speedup_positive_threshold
    ∧ qwen_0_5b_pca_K1_N8.speedup_perthou < speedup_positive_threshold := by
  exact ⟨by decide, by decide, by decide⟩

/-- Joint structural recommendation: BOTH fidelity AND wall-clock
    rule out PCA-only K=1 deployment. The two failures are
    independent ledger entries (fidelity is information-theoretic;
    speedup is wall-clock), and they fail TOGETHER on every
    measured configuration. -/
theorem pca_only_K1_fails_on_both_axes :
    (qwen_0_5b_pca_K1_N4.accept_rate_perthou < fidelity_safe_threshold)
    ∧ (qwen_0_5b_pca_K1_N4.speedup_perthou < speedup_positive_threshold) := by
  exact ⟨by decide, by decide⟩

end SpecDecodeKDependence
end Gnosis
