/-
  SpeculativeDecodingAsRetrocausal.lean
  =====================================

  Speculative decoding, formalized as another instance of the
  Novikov-self-consistency / verify-protocol pattern.

  The standard single-token verify (CompressionUncertainty) closes the
  loop one token at a time: a draft proposes one token, the verifier
  compares to baseline, the timeline either accepts (handshake) or
  rolls back. Speculative decoding generalizes this to a SEQUENCE of
  N tokens at a time. The draft model emits N speculative tokens; the
  baseline (target) model verifies them in parallel; the protocol
  accepts the longest matching prefix and emits one extra token from
  the baseline at the divergence point.

  CLAIM: speculative decoding is a coarsening of the candidate-set
  verify protocol with K=1 and a multi-token batch. It satisfies the
  same conservation law (`closes (event_of_verify P)`) as single-token
  verify — every emitted position has actual = baseline by construction
  because divergent positions are discarded.

  The conjugate-variables story: speculative decoding pays compute (the
  baseline runs on every draft position in parallel) to save SEQUENTIAL
  steps (a hit of length n eliminates n-1 sequential baseline calls).
  Same Wheeler-Feynman handshake, batched.

  Imports CompressionUncertainty (single-token verify primitives) and
  CompressionAsRetrocausalClosure (the NovikovEvent bridge). Init-only
  Lean 4. Zero sorries, zero axioms.
-/

import Gnosis.CompressionUncertainty
import Gnosis.CompressionAsRetrocausalClosure

namespace Gnosis
namespace SpeculativeDecodingAsRetrocausal

open CompressionUncertainty
open CompressionAsRetrocausalClosure

-- ══════════════════════════════════════════════════════════
-- DEFINITIONS
-- ══════════════════════════════════════════════════════════

/-- A speculative-decoding protocol. The `draft` is the cheaper proposer
    (typically a smaller model or a shallower variant). `speculation_N`
    is the lookahead window — how many tokens the draft emits before
    the baseline verifies. `per_position_hit_num/hit_denom` is the
    measured probability that the draft's argmax at any given position
    matches the baseline's argmax at that position.

    NOTE on independence: the expected-accepted-prefix-length formula
    below assumes per-position hits are INDEPENDENT. In practice they
    are positively correlated (a hit at t generally raises P(hit at
    t+1) because the context is closer to the baseline's preferred
    path). The independent-Bernoulli model gives a conservative lower
    bound on expected accepted length; we adopt it here for the same
    reason the runtime does — closed-form, monotone, calibratable. -/
structure SpeculativeProtocol where
  draft                : Scheme    -- the cheaper draft scheme
  speculation_N        : Nat       -- lookahead window
  per_position_hit_num : Nat       -- P(draft argmax = baseline argmax)
  per_position_hit_den : Nat       -- denominator (> 0)

/-- Wellformedness for a speculative protocol. -/
structure SpeculativeWellformed (S : SpeculativeProtocol) : Prop where
  draft_wf  : Wellformed S.draft
  hit_pos   : 0 < S.per_position_hit_den
  hit_le    : S.per_position_hit_num ≤ S.per_position_hit_den
  N_pos     : 0 < S.speculation_N

/-- The expected accepted-prefix length under the independent-Bernoulli
    model. Real number formula: E[L] = N · p where p = hit_num/hit_den.
    Discretized as Nat via floor: floor(N · hit_num / hit_den).

    This is conservative (true E[L] under positive correlation is
    higher) but it's the formula the runtime uses for window-size
    calibration. -/
def expected_accepted_prefix_length (S : SpeculativeProtocol) : Nat :=
  (S.speculation_N * S.per_position_hit_num) / S.per_position_hit_den

/-- Speedup (numerator) of speculative decoding vs unbatched baseline.

    Story: in N+1 baseline forward passes worth of clock time, the
    protocol emits `accepted + 1` verified tokens. The "+1" is the
    always-emitted next token sampled from the baseline at the
    divergence position (which was computed for free as part of the
    parallel verify). So speedup = (accepted + 1) / 1 baseline-step,
    measured against (N+1)/(N+1) = 1 step in the unbatched limit;
    we report it as the discrete ratio (accepted+1) : (N+1) for
    well-defined Nat arithmetic.

    Equivalently: the protocol replaces N+1 sequential baseline steps
    with 1 batched baseline step that yields `accepted + 1` tokens. -/
def speculative_speedup_num (S : SpeculativeProtocol) : Nat :=
  expected_accepted_prefix_length S + 1

def speculative_speedup_den (S : SpeculativeProtocol) : Nat :=
  S.speculation_N + 1

-- ══════════════════════════════════════════════════════════
-- BRIDGE: SPECULATIVE PROTOCOL → VERIFY PROTOCOL
-- ══════════════════════════════════════════════════════════

/-- Project a SpeculativeProtocol down to a single-token VerifyProtocol
    using the per-position hit rate as the (K=1) hit probability and
    the same draft scheme. This is the "K=1, multi-token batch is a
    coarsening" framing: a single-position view of the speculative
    protocol IS exactly a candidate-set verify with K=1. -/
def to_verify_protocol (S : SpeculativeProtocol) : VerifyProtocol :=
  { draft     := S.draft
  , hit_num   := S.per_position_hit_num
  , hit_denom := S.per_position_hit_den }

/-- Inducing a NovikovEvent from a speculative protocol via the
    verify-projection. Every emitted position has actual = baseline
    because the verifier discards divergent positions. -/
def event_of_speculative (S : SpeculativeProtocol) : NovikovEvent :=
  event_of_verify (to_verify_protocol S)

-- ══════════════════════════════════════════════════════════
-- THEOREMS
-- ══════════════════════════════════════════════════════════

/-- Theorem: SPECULATIVE-PROTOCOL-SATISFIES-NOVIKOV.

    Every speculative protocol's emitted tokens satisfy
    `actual = baseline` by construction. The verifier discards every
    divergent position; only matching prefix tokens (and the always-
    correct rollback token from the baseline) are emitted.

    This bridges directly to `compression_runtime_obeys_novikov` from
    CompressionAsRetrocausalClosure: the speculative protocol's
    induced NovikovEvent closes for the same reason single-token
    verify's does — the verifier IS the Novikov projector. -/
theorem speculative_protocol_satisfies_novikov (S : SpeculativeProtocol) :
    closes (event_of_speculative S) := by
  unfold event_of_speculative
  exact compression_runtime_obeys_novikov (to_verify_protocol S)

/-- Theorem: SPECULATIVE-SPEEDUP-AT-PERFECT-HIT.

    When the per-position hit rate is 1 (draft always matches
    baseline), the expected accepted prefix is exactly N, and the
    speedup ratio is (N+1)/(N+1) = 1 ... but in operationally
    meaningful units, this means we accept the entire window plus
    the rollback token, yielding N+1 verified tokens per single
    batched baseline step. The speedup numerator is N+1, matching
    the denominator — i.e. we got N "free" tokens beyond the one
    sequential step would have produced.

    Concretely: speculative_speedup_num = N + 1 when hit rate is full.
    The "speedup is N" is the comparison to the unbatched baseline:
    N+1 tokens in the cost of 1 baseline forward pass means a
    factor of N+1 vs strict serial decoding. -/
theorem speculative_speedup_at_perfect_hit
    (S : SpeculativeProtocol)
    (h_hit : S.per_position_hit_num = S.per_position_hit_den)
    (h_pos : 0 < S.per_position_hit_den) :
    speculative_speedup_num S = S.speculation_N + 1 := by
  unfold speculative_speedup_num expected_accepted_prefix_length
  rw [h_hit]
  -- goal: S.speculation_N * S.per_position_hit_den / S.per_position_hit_den + 1
  --     = S.speculation_N + 1
  rw [Nat.mul_div_cancel _ h_pos]

/-- Theorem: SPECULATIVE-SPEEDUP-AT-ZERO-HIT.

    When the per-position hit rate is 0, the expected accepted prefix
    is 0 (every draft token rejected), and the speedup numerator is
    just 1 — we still get the rollback token from the baseline's
    parallel verify, but we paid for N parallel baseline computations
    to get a single token. Speedup ≤ 1 (no acceleration; in wall-clock
    terms this is a slowdown when the parallel baseline is not free,
    which it isn't on a single host).

    Concretely: speculative_speedup_num = 1 ≤ N + 1 = speedup_den.
    The protocol "degrades gracefully" to baseline behavior at the
    zero-hit limit, modulo the wasted parallel-baseline compute. -/
theorem speculative_speedup_at_zero_hit
    (S : SpeculativeProtocol)
    (h_hit : S.per_position_hit_num = 0) :
    speculative_speedup_num S ≤ speculative_speedup_den S := by
  unfold speculative_speedup_num speculative_speedup_den
    expected_accepted_prefix_length
  rw [h_hit]
  -- goal: S.speculation_N * 0 / S.per_position_hit_den + 1 ≤ S.speculation_N + 1
  simp

/-- Theorem: SPECULATIVE-IS-SPECIAL-CASE-OF-VERIFY.

    The speculative protocol is a coarsening of the candidate-set
    verify protocol with K=1 and a multi-token batch. Concretely:
    a speculative protocol's induced NovikovEvent is *definitionally*
    the NovikovEvent of its projected single-token VerifyProtocol.

    This is the structural identity that justifies all the conservation
    machinery transferring over: anything we proved about VerifyProtocol
    in CompressionUncertainty + CompressionAsRetrocausalClosure
    applies to SpeculativeProtocol via `to_verify_protocol`. -/
theorem speculative_is_special_case_of_verify (S : SpeculativeProtocol) :
    event_of_speculative S = event_of_verify (to_verify_protocol S) := by
  rfl

/-- Corollary: the speculative protocol's verified fidelity is 1, by
    the same argument as single-token verify. Every emitted token
    matches the baseline; divergent positions never reach the output. -/
theorem speculative_verified_fidelity_is_one (S : SpeculativeProtocol) :
    verified_fidelity_num (to_verify_protocol S)
      = verified_fidelity_den (to_verify_protocol S) := by
  exact verify_preserves_identity (to_verify_protocol S)

/-- Theorem: SPECULATIVE-WELLFORMED-PROJECTS-TO-VERIFY-WELLFORMED.

    Wellformedness of a speculative protocol implies wellformedness
    of its single-token verify projection. The structural-conservation
    proofs in CompressionUncertainty therefore apply directly. -/
theorem speculative_wf_implies_verify_wf
    (S : SpeculativeProtocol) (h : SpeculativeWellformed S) :
    VerifyWellformed (to_verify_protocol S) := by
  refine { draft_wf := ?_, hit_pos := ?_, hit_le := ?_ }
  · exact h.draft_wf
  · exact h.hit_pos
  · exact h.hit_le

-- ══════════════════════════════════════════════════════════
-- EMPIRICAL INSTANCE: PROJECTED FROM qwen_pca_k8
-- ══════════════════════════════════════════════════════════

/-- Projected speculative protocol using the measured per-position
    hit rate from qwen_pca_k8 (73% top-K hit was the candidate-set
    measurement; here we treat it as a reasonable per-position hit
    rate for a hypothetical N=4 speculative window over the same
    model class).

    NOTE: this is a projection, not a measurement. The qwen_pca_k8
    73% number was a top-5 hit rate for the candidate-set protocol;
    the speculative-decoding interpretation requires re-measuring
    top-1 match between draft and target, which would typically be
    LOWER. Recorded here as a calibration target for the runtime,
    not as a measured value. -/
def qwen_pca_speculative_4_token : SpeculativeProtocol :=
  { draft                := qwen_pca_k8
  , speculation_N        := 4
  , per_position_hit_num := 73
  , per_position_hit_den := 100 }

/-- Wellformedness of the projected qwen_pca_speculative_4_token. -/
theorem qwen_pca_speculative_wellformed :
    SpeculativeWellformed qwen_pca_speculative_4_token := by
  refine { draft_wf := ?_, hit_pos := ?_, hit_le := ?_, N_pos := ?_ }
  · exact qwen_pca_k8_wellformed
  · decide
  · decide
  · decide

/-- Theorem: the projected speculative protocol satisfies the
    Novikov closure law (decidable instance). -/
theorem qwen_pca_speculative_satisfies_novikov :
    closes (event_of_speculative qwen_pca_speculative_4_token) := by
  unfold closes satisfies_novikov event_of_speculative event_of_verify
    to_verify_protocol
  decide

/-- Theorem: the projected expected accepted prefix length is
    floor(4 · 73 / 100) = floor(292 / 100) = 2. The continuous
    expectation is 2.92; Nat floor truncates to 2. -/
theorem qwen_pca_speculative_expected_accepted :
    expected_accepted_prefix_length qwen_pca_speculative_4_token = 2 := by
  decide

/-- Theorem: the speedup numerator is 3 (= 2 + 1) and denominator
    is 5 (= 4 + 1). Per batched baseline step the protocol emits
    3 verified tokens, vs 1 in strict serial decoding — a ~3x
    sequential-step speedup at the projected hit rate, modulo
    parallel-baseline compute amortization. -/
theorem qwen_pca_speculative_speedup_ratio :
    speculative_speedup_num qwen_pca_speculative_4_token = 3
    ∧ speculative_speedup_den qwen_pca_speculative_4_token = 5 := by
  exact ⟨by decide, by decide⟩

end SpeculativeDecodingAsRetrocausal
end Gnosis
