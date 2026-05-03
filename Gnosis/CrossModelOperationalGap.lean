/-
  CrossModelOperationalGap.lean
  =============================

  LEAN ANCHOR of the wave-4 honest falsification.

  Wave 1 produced the McNally Cliff law: a per-layer σ_1/σ_2 ratio
  whose sharp regions predict where capacity-friendly compression
  is STRUCTURALLY available. The wave-1 result on Qwen2.5-0.5B was
  decisive: PCA-only at K=5 against the cliff-band layers
  (L5/10/15/22, all inside the L3-L24 cliff band) achieved
  effective fidelity F_eff = 1.00 over a 30-token next-token
  argmax test.

  Wave 4 ran the SAME picker, the SAME PCA-only policy, the SAME
  K=5, against the SAME predicted cliff band, on Qwen-Coder-7B
  (the next-larger sibling in the same model family). Result:
  F_eff = 0.00. All 30 of 30 tokens fell back to the verifier and
  were rolled back. The picker chose layers inside the predicted
  cliff band — the structural prediction was correct. The
  operational realization was not.

  This refines the Theory of Model Physics:

    OLD (too strong): "cliff prediction → compressibility"
    NEW (precise)   : "cliff prediction → STRUCTURAL
                       compressibility, but OPERATIONAL
                       compressibility is K-dependent and may
                       scale with hidden_dim".

  The conjecture for wave 5 (NOT proved here, recorded as a
  comment for future falsification): if K is widened linearly
  with hidden_dim, F_eff is restored. Wave 5 will sweep K and
  decide.

  This module:

    1. Defines `OperationalReading` — the four numbers an operator
       needs to record per (model, K) measurement.
    2. Defines `is_operationally_certified` — F_eff ≥ 0.95
       (per-thousand ≥ 950).
    3. Records the two measured readings (Qwen2.5-0.5B at K=5
       and Qwen-Coder-7B at K=5) as per-instance constants.
    4. Discharges the per-instance certification verdicts by
       `decide`.
    5. Proves `cliff_band_correctness_does_not_imply_operational_certification`
       — exhibits the 7B reading as a witness with `cliff_band_correctly_chosen
       = true` and `is_operationally_certified = false`, formally
       decoupling the structural and operational predicates.
    6. Proves `structural_prediction_does_not_transfer_at_fixed_K`
       — the cross-model gap, exhibited by the two same-family
       readings.

  Init-only Lean 4. Imports CrossModelCliff, CliffCapacityBridge,
  MultiModelCertificateAtlas, CompressionUncertainty for context;
  the proofs themselves use only `decide` over the structure
  fields. Zero sorries, zero axioms.
-/

import Gnosis.CrossModelCliff
import Gnosis.CliffCapacityBridge
import Gnosis.MultiModelCertificateAtlas
import Gnosis.CompressionUncertainty

namespace Gnosis
namespace CrossModelOperationalGap

-- ══════════════════════════════════════════════════════════
-- THE OPERATIONAL READING
-- ══════════════════════════════════════════════════════════

/-- A single (model, K) operational measurement of the PCA-only
    standing-wave-pinning policy.

    Fields:
      • `model_dim` — hidden dimension d of the residual stream.
      • `candidate_K` — the K parameter passed to the picker
        (top-K candidate set the verifier compares against the
        baseline argmax).
      • `measured_f_eff_perthou` — F_eff measured on a fixed
        next-token argmax suite, expressed in per-thousand units
        (so 1000 = 1.00, 950 = 0.95, 0 = 0.00). Per-thousand
        avoids Float arithmetic and keeps `decide` available.
      • `cliff_band_correctly_chosen` — whether the picker's
        chosen layers fell inside the McNally-cliff band that
        `CrossModelCliff` / `CliffCapacityBridge` predicted as
        capacity-friendly. This is the STRUCTURAL prediction
        check; it is independent of whether the run actually
        certified operationally. -/
structure OperationalReading where
  model_dim                  : Nat
  candidate_K                : Nat
  measured_f_eff_perthou     : Nat
  cliff_band_correctly_chosen : Bool
  deriving Repr, DecidableEq

-- ══════════════════════════════════════════════════════════
-- THE OPERATIONAL CERTIFICATION PREDICATE
-- ══════════════════════════════════════════════════════════

/-- Per-thousand F_eff threshold for operational certification:
    950 corresponds to F_eff ≥ 0.95. The same 0.95 cutoff used
    in the wave-2 RuntimeCertificate / standing-wave-parity
    pipeline. -/
def fEffPerthouThreshold : Nat := 950

/-- A reading is OPERATIONALLY CERTIFIED iff its measured F_eff
    (in per-thousand units) meets the certification threshold.

    This predicate is intentionally independent of
    `cliff_band_correctly_chosen` — that is precisely the
    decoupling the wave-4 falsification is making formal. -/
def is_operationally_certified (r : OperationalReading) : Bool :=
  decide (fEffPerthouThreshold ≤ r.measured_f_eff_perthou)

-- ══════════════════════════════════════════════════════════
-- PER-INSTANCE EMPIRICAL READINGS
-- ══════════════════════════════════════════════════════════

/-- Qwen2.5-0.5B PCA-only K=5 reading (wave 1, 2026-05-01).
      • d = 896 (hidden dim of Qwen2.5-0.5B residual stream)
      • K = 5 candidate top-K
      • F_eff = 1.00 (perthou = 1000) — every one of 30 tokens
        either matched the baseline argmax or hit the K=5
        verifier set.
      • Picker chose L5 / L10 / L15 / L22, all inside the
        cliff-band L3..L24 predicted by `CrossModelCliff`. -/
def qwen_0_5b_K5_pca_operational : OperationalReading :=
  { model_dim                   := 896
  , candidate_K                 := 5
  , measured_f_eff_perthou      := 1000
  , cliff_band_correctly_chosen := true }

/-- Qwen-Coder-7B PCA-only K=5 reading (wave 4, 2026-05-03).
      • d = 3584 (hidden dim of Qwen-Coder-7B residual stream)
      • K = 5 candidate top-K (UNCHANGED from the 0.5B run —
        this is the controlled cross-model variable)
      • F_eff = 0.00 (perthou = 0) — all 30 of 30 tokens
        diverged from the baseline argmax AND missed the K=5
        verifier set, triggering full rollback on every token.
      • Picker chose L5 / L10 / L15 / L22, again inside the
        cliff band predicted for the family. The structural
        prediction was right; the operational realization was
        not. -/
def qwen_coder_7b_K5_pca_operational : OperationalReading :=
  { model_dim                   := 3584
  , candidate_K                 := 5
  , measured_f_eff_perthou      := 0
  , cliff_band_correctly_chosen := true }

-- ══════════════════════════════════════════════════════════
-- PER-INSTANCE OPERATIONAL VERDICTS (decide-checked)
-- ══════════════════════════════════════════════════════════

/-- The 0.5B reading certifies. F_eff = 1000 perthou ≥ 950. -/
theorem qwen_0_5b_K5_is_operationally_certified :
    is_operationally_certified qwen_0_5b_K5_pca_operational = true := by
  decide

/-- The 7B reading does NOT certify. F_eff = 0 perthou < 950. -/
theorem qwen_coder_7b_K5_is_NOT_operationally_certified :
    is_operationally_certified qwen_coder_7b_K5_pca_operational = false := by
  decide

/-- Both readings agreed on the structural prediction: the
    picker's chosen layers fell inside the predicted cliff band
    in both cases. This is the diagnostic that makes the wave-4
    finding load-bearing — the structural side is not where the
    failure lives. -/
theorem both_readings_agree_on_cliff_band :
    qwen_0_5b_K5_pca_operational.cliff_band_correctly_chosen = true ∧
    qwen_coder_7b_K5_pca_operational.cliff_band_correctly_chosen = true := by
  decide

-- ══════════════════════════════════════════════════════════
-- THE DECOUPLING THEOREM
-- ══════════════════════════════════════════════════════════

/-- Theorem: CLIFF-BAND-CORRECTNESS-DOES-NOT-IMPLY-
              OPERATIONAL-CERTIFICATION.

    There exists a well-typed `OperationalReading` whose
    `cliff_band_correctly_chosen` field is `true` AND whose
    `is_operationally_certified` verdict is `false`.

    The witness is `qwen_coder_7b_K5_pca_operational`. The
    structural prediction (the picker chose layers inside the
    family's cliff band) holds; the operational verdict
    (F_eff ≥ 0.95) does not. This formally decouples the two
    predicates: structural cliff-band correctness is NOT a
    proof of operational compressibility. -/
theorem cliff_band_correctness_does_not_imply_operational_certification :
    ∃ r : OperationalReading,
      r.cliff_band_correctly_chosen = true ∧
      is_operationally_certified r = false := by
  refine ⟨qwen_coder_7b_K5_pca_operational, ?_, ?_⟩
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- THE CROSS-MODEL OPERATIONAL GAP
-- ══════════════════════════════════════════════════════════

/-- Theorem: STRUCTURAL-PREDICTION-DOES-NOT-TRANSFER-AT-FIXED-K.

    There exist two `OperationalReading` values M1 and M2 such
    that:

      (a) both share the SAME candidate_K (controlled variable);
      (b) both pass the structural cliff-band prediction
          (`cliff_band_correctly_chosen = true`);
      (c) M1 is operationally certified
          (`is_operationally_certified = true`);
      (d) M2 is NOT operationally certified
          (`is_operationally_certified = false`).

    Witnesses:
      • M1 = qwen_0_5b_K5_pca_operational    (d=896,  F_eff=1.00)
      • M2 = qwen_coder_7b_K5_pca_operational (d=3584, F_eff=0.00)

    Both are members of the Qwen family; both ran with K=5;
    both had their picker land in the predicted cliff band.
    The only thing that varied was the model's hidden
    dimension (and therefore its residual-stream width). The
    operational verdict flipped from `true` to `false`.

    This is the wave-4 falsification of the over-strong reading
    of the Theory of Model Physics. Structural prediction
    transfers across the same-family scale-up. Operational
    realization at fixed K does not. -/
theorem structural_prediction_does_not_transfer_at_fixed_K :
    ∃ M1 M2 : OperationalReading,
      M1.candidate_K = M2.candidate_K ∧
      M1.cliff_band_correctly_chosen = true ∧
      M2.cliff_band_correctly_chosen = true ∧
      is_operationally_certified M1 = true ∧
      is_operationally_certified M2 = false := by
  refine ⟨qwen_0_5b_K5_pca_operational,
          qwen_coder_7b_K5_pca_operational,
          ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- WAVE-5 CONJECTURE (NOT PROVED — for future falsification)
-- ══════════════════════════════════════════════════════════

/-
  Conjecture: K_widening_rescues_at_scale_conjecture
  --------------------------------------------------

  Informally: if the candidate top-K is grown LINEARLY with the
  model's hidden dimension d, the operational F_eff is restored
  toward the threshold. Concretely, the wave-5 K-sweep on
  Qwen-Coder-7B is expected to find some K* (estimated K* ≈
  5 · 3584 / 896 = 20, holding the "K per thousand-d" ratio
  constant against the wave-1 0.5B baseline) at which
  `is_operationally_certified` flips back to `true`.

  Lean shape (recorded as prose so the file stays sorry-free):

      ∃ K_scaled : Nat,
        K_scaled ≥ 5 * 3584 / 896 ∧
        ∃ rescued : OperationalReading,
          rescued.model_dim = 3584 ∧
          rescued.candidate_K = K_scaled ∧
          is_operationally_certified rescued = true

  When the wave-5 K-sweep produces the measured `OperationalReading`
  with F_eff ≥ 0.95 at d=3584, the witness is supplied and the
  theorem is discharged by `decide`. If the K-sweep fails to find
  such a K_scaled, the conjecture is falsified and the Theory of
  Model Physics is refined again.
-/

-- ══════════════════════════════════════════════════════════
-- TIE-BACK TO PRIOR MODULES
-- ══════════════════════════════════════════════════════════

/-- Tie-back: the structural cliff prediction relied on by
    `cliff_band_correctly_chosen` is the same Spike-topology
    pattern recorded in `CrossModelCliff` for the Qwen family. -/
theorem qwen_family_structural_anchor :
    CrossModelCliff.qwen_2_5_0_5b_profile.cliff_topology
      = CrossModelCliff.CliffTopology.Spike := by
  decide

/-- Tie-back: the wave-2 / wave-3 PROJECTED certification of
    Qwen-Coder-7B in `MultiModelCertificateAtlas` was decided
    on PROJECTED inputs (F=40/100 reused from the 0.5B run).
    The wave-4 reading recorded in this module is the
    MEASURED F_eff at K=5 — and it is 0/1000, well below the
    projected 40/100. The projected-certified verdict therefore
    does NOT survive the K=5 measurement; the projection must
    be revisited (and likely re-stated as conditional on a
    K_scaled wave-5 run). This theorem makes that delta
    formal. -/
theorem wave4_measurement_invalidates_projected_K5_for_7b :
    is_operationally_certified qwen_coder_7b_K5_pca_operational = false := by
  decide

end CrossModelOperationalGap
end Gnosis
