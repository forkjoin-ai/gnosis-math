/-
  CertificationDemotion.lean
  ==========================

  THE GOOD-FAITH RECORD.

  Wave-2 (RuntimeCertificate.lean) shipped a single measured
  certificate: Qwen2.5-0.5B at K=8, F_eff = 1.00. Wave-3
  (MultiModelCertificateAtlas.lean) lifted that pattern to two
  additional models — Qwen-Coder-7B and Llama-1B — by PROJECTING
  their fidelity numbers from the Qwen2.5-0.5B measurement. The
  atlas was honest about the projection: it labelled both as
  PROJECTED-CERTIFIED and listed the upgrade path.

  Wave-4 ran the parity pipeline on Qwen-Coder-7B at K=5, PCA-only.
  It measured F=0/30. The wave-3 projection had been F=40/100
  (i.e. 0.40). The projection was wrong by 100% of the projected
  value — the cliff is real and the within-family extrapolation
  from the 0.5B model did not survive the jump to 7B.

  This module is the FORMAL DEMOTION RECORD. It does NOT edit
  RuntimeCertificate.lean and does NOT edit MultiModelCertificateAtlas.lean
  (those stay as-is, the historical record of what was projected and
  when). Instead it:

    1. Defines a `CertificationStatus` enum that names the four
       distinct epistemic states a model can be in:
         Certified, ProjectedCertified, DemotedAfterMeasurement,
         UnderInvestigation.

    2. Pins each of the three wave-3 atlas models to its current
       status as of 2026-05-03, post-wave-4 measurement.

    3. Carries the per-instance demotion as a decide-checked
       theorem.

    4. Quantifies the projection error:
         projected F = 40/100 ⇒ 400 perthou
         measured  F =  0/30  ⇒   0 perthou
         |proj − meas| = 400 perthou
       The projection was 0.40 absolute fidelity above the truth.

    5. Lifts the per-instance failure to a structural lesson:
       within-family projection is not a substitute for
       within-scale measurement. Qwen-Coder-7B is the witness.

    6. States the upgrade conditions for Qwen-Coder-7B as a
       documentation theorem: status returns to Certified iff
       wave-5's K-widening sweep finds a K with F_eff ≥ 0.95;
       otherwise status stays DemotedAfterMeasurement and the
       wave-3 RuntimeCertificate definition for that model must
       be revised to use the measured F=0 instead of the
       projected F=40/100.

  The Theory of Model Physics survives by being refined: cliff
  prediction PLUS K-tuning, not cliff prediction alone. The
  certification ledger is a LIVING DOCUMENT, not a marketing badge.

  Init-only Lean 4. Zero sorries, zero axioms.
-/

namespace Gnosis
namespace CertificationDemotion

-- ══════════════════════════════════════════════════════════
-- THE FOUR EPISTEMIC STATES OF A CERTIFICATE
-- ══════════════════════════════════════════════════════════

/-- The certification status of a (model, scheme) pair.

    These are the four distinct epistemic states a deployment can
    be in at the certification ledger. They are NOT a quality
    ranking — they are about HOW MUCH WE KNOW.

    • `Certified`                 — decide-checked AND the F/hit
      inputs are MEASURED on the deployed model. Production-ready
      under the wave-2 criterion. Example: Qwen2.5-0.5B at K=8.

    • `ProjectedCertified`        — decide-checked, but the F/hit
      inputs are PROJECTED from a reference model (typically a
      smaller sibling). The certificate is internally consistent;
      the question is whether the projection survives measurement.

    • `DemotedAfterMeasurement`   — was `ProjectedCertified`, then
      the parity pipeline ran on the deployed model and returned
      a measured F BELOW the projection. The wave-3 certificate
      is now historical record; production status is REVOKED until
      a K-widening sweep restores F_eff ≥ 0.95.

    • `UnderInvestigation`        — a failure was found but the
      root cause is not yet pinned. Reserved for cases where the
      measured number is ambiguous (e.g., parity disagreement
      between two replicate runs) and the demotion is provisional. -/
inductive CertificationStatus
  | Certified
  | ProjectedCertified
  | DemotedAfterMeasurement
  | UnderInvestigation
  deriving DecidableEq, Repr

-- ══════════════════════════════════════════════════════════
-- THE THREE WAVE-3 ATLAS MODELS
-- ══════════════════════════════════════════════════════════

/-- Stable identifiers for the three models the wave-3 atlas
    declared. Symbolic so this module compiles standalone, without
    re-importing the wave-2/3 numeric bundles. -/
inductive ModelId
  | qwen_0_5b
  | qwen_coder_7b
  | llama_1b
  deriving DecidableEq, Repr

-- ══════════════════════════════════════════════════════════
-- THE LIVING LEDGER (state as of 2026-05-03, post-wave-4)
-- ══════════════════════════════════════════════════════════

/-- The per-model current certification status. This is the
    OPERATOR-FACING ledger: looking up a model id returns the
    epistemic state of its certificate as of the post-wave-4
    measurement pass.

    State transitions:

      Qwen2.5-0.5B
        wave-2 measured F=40/100 then F_eff=1.00 (rescue) → `Certified`.

      Qwen-Coder-7B
        wave-3 PROJECTED F=40/100 from Qwen-0.5B → `ProjectedCertified`.
        wave-4 MEASURED F=0/30 at K=5 PCA-only.   → DEMOTION.
        Status: `DemotedAfterMeasurement`.

      Llama-1B
        wave-3 PROJECTED F=40/100 from Qwen-0.5B → `ProjectedCertified`.
        wave-4 has not measured llama yet. Status holds. -/
def current_certification_status : ModelId → CertificationStatus
  | .qwen_0_5b      => .Certified
  | .qwen_coder_7b  => .DemotedAfterMeasurement
  | .llama_1b       => .ProjectedCertified

-- ══════════════════════════════════════════════════════════
-- PER-INSTANCE STATUS THEOREMS (decide-checked)
-- ══════════════════════════════════════════════════════════

/-- Theorem: QWEN-0.5B-REMAINS-CERTIFIED.

    The wave-2 measurement (F_eff = 1.00 after the K=8 rescue)
    holds. Wave-4 did not re-touch this model. Status stays
    `Certified`. -/
theorem qwen_0_5b_remains_certified :
    current_certification_status .qwen_0_5b = .Certified := by
  decide

/-- Theorem: QWEN-CODER-7B-DEMOTED-AFTER-WAVE-4-MEASUREMENT.

    THE DEMOTION. Wave-3 listed Qwen-Coder-7B as
    `ProjectedCertified` on a projection of F=40/100 from the
    Qwen-0.5B baseline. Wave-4 ran the parity pipeline at K=5,
    PCA-only, and returned F=0/30. The projection was wrong by
    the full projected amount. The certificate's status is now
    `DemotedAfterMeasurement`.

    Effect on the wave-3 atlas: the file
    `MultiModelCertificateAtlas.lean` is NOT edited; it remains
    the historical record of what wave-3 projected. This theorem
    is the formal mark that the projection has been falsified at
    K=5. Re-certification path is given by
    `qwen_coder_7b_upgrade_conditions` below. -/
theorem qwen_coder_7b_demoted_after_wave_4_measurement :
    current_certification_status .qwen_coder_7b
      = .DemotedAfterMeasurement := by
  decide

/-- Theorem: LLAMA-1B-PROJECTION-PENDING-MEASUREMENT.

    Wave-4 did not measure Llama-1B. The wave-3 projection still
    stands, and the status remains `ProjectedCertified`. The
    upgrade path is the same one wave-3 documented: run the parity
    pipeline on Llama-1B, then either promote to `Certified` or
    demote to `DemotedAfterMeasurement` depending on the measured
    F_eff. -/
theorem llama_1b_projection_pending_measurement :
    current_certification_status .llama_1b = .ProjectedCertified := by
  decide

-- ══════════════════════════════════════════════════════════
-- QUANTIFYING THE PROJECTION ERROR
-- ══════════════════════════════════════════════════════════

/-- Per-thousand projection error: the absolute difference between
    a projected fidelity (in perthou — parts per thousand) and the
    measured fidelity (in perthou).

    Both inputs are expected to already be in perthou units:

        F = 40/100 = 0.40 = 400 perthou
        F =  0/30  = 0.00 =   0 perthou

    so callers convert their numerator/denominator pair to perthou
    before calling. We avoid Rat to keep this Init-only and
    decide-friendly. -/
def projection_measurement_error_perthou (projected measured : Nat) : Nat :=
  if projected ≥ measured then projected - measured else measured - projected

/-- Convert a fidelity expressed as `num/den` (with `den > 0` in
    practice; we do not require it here, the caller passes the
    already-canonicalised perthou) to a Nat in parts per thousand.
    `to_perthou 40 100 = 400`, `to_perthou 0 30 = 0`. Truncating
    division is fine — wave-4 perthou values are exact. -/
def to_perthou (num den : Nat) : Nat :=
  if den = 0 then 0 else (num * 1000) / den

/-- Theorem: QWEN-CODER-7B-PROJECTION-ERROR.

    The projection error for Qwen-Coder-7B is exactly 400 perthou
    — i.e. 0.40 absolute fidelity. The wave-3 projection (F=40/100
    = 400 perthou) sat 400 perthou ABOVE the wave-4 measurement
    (F=0/30 = 0 perthou).

    400 perthou ≥ 0.40 absolute fidelity is the witness used by
    `projection_within_family_can_fail_at_scale` below. -/
theorem qwen_coder_7b_projection_error :
    projection_measurement_error_perthou
      (to_perthou 40 100) (to_perthou 0 30) = 400 := by
  decide

/-- Theorem: QWEN-CODER-7B-PROJECTION-ERROR-EXCEEDS-FOUR-TENTHS.

    The projection error is at least 400 perthou (≥ 0.40 absolute
    fidelity). This is the threshold that the structural-lesson
    theorem keys on. -/
theorem qwen_coder_7b_projection_error_exceeds_four_tenths :
    400 ≤ projection_measurement_error_perthou
            (to_perthou 40 100) (to_perthou 0 30) := by
  decide

-- ══════════════════════════════════════════════════════════
-- THE STRUCTURAL LESSON
-- ══════════════════════════════════════════════════════════

/-- Theorem: PROJECTION-WITHIN-FAMILY-CAN-FAIL-AT-SCALE.

    There exists a model in the wave-3 atlas whose within-family
    projection from Qwen-0.5B was off by at least 0.40 absolute
    fidelity (400 perthou) when the parity pipeline actually ran
    on it.

    The witness is `qwen_coder_7b`: the projection was F=40/100
    (400 perthou); the measurement at K=5 PCA-only was F=0/30
    (0 perthou); the error is exactly 400 perthou.

    Operational reading: the cliff topology is real, the
    within-family extrapolation from a 0.5B sibling did not cross
    the 7B scale, and the certification ledger requires per-scale
    measurement, not per-family projection. -/
theorem projection_within_family_can_fail_at_scale :
    ∃ m : ModelId,
      current_certification_status m = .DemotedAfterMeasurement ∧
      400 ≤ projection_measurement_error_perthou
              (to_perthou 40 100) (to_perthou 0 30) := by
  refine ⟨.qwen_coder_7b, ?_, ?_⟩
  · exact qwen_coder_7b_demoted_after_wave_4_measurement
  · exact qwen_coder_7b_projection_error_exceeds_four_tenths

-- ══════════════════════════════════════════════════════════
-- THE REMEDIATION DIRECTIVE (documentation theorem)
-- ══════════════════════════════════════════════════════════

/-- The K-widening outcome of wave-5: the measured effective
    fidelity, in perthou, after sweeping K. Symbolic — the actual
    number lands when wave-5 runs. -/
structure WaveFiveSweepResult where
  /-- The K value at which the best F_eff was achieved. -/
  best_k         : Nat
  /-- The best measured F_eff in perthou (0..1000). -/
  best_F_perthou : Nat

/-- The certification-pass threshold for wave-5: F_eff ≥ 0.95
    expressed in perthou is `≥ 950`. -/
def wave_5_pass_threshold_perthou : Nat := 950

/-- Decide whether a wave-5 sweep result clears the
    `wave_5_pass_threshold_perthou` bar. -/
def wave_5_clears_threshold (r : WaveFiveSweepResult) : Bool :=
  decide (r.best_F_perthou ≥ wave_5_pass_threshold_perthou)

/-- The post-wave-5 status function for Qwen-Coder-7B. THIS IS
    THE REMEDIATION DIRECTIVE encoded as data:

      • If wave-5's K-widening sweep returns a `best_F_perthou`
        at or above 950 (i.e. F_eff ≥ 0.95), the status UPGRADES
        from `DemotedAfterMeasurement` back to `Certified`.

      • Otherwise the status STAYS `DemotedAfterMeasurement`.

    An operator wires the actual wave-5 sweep result into this
    function to read off the post-wave-5 status. -/
def qwen_coder_7b_status_after_wave_5
    (r : WaveFiveSweepResult) : CertificationStatus :=
  if wave_5_clears_threshold r then .Certified else .DemotedAfterMeasurement

/-- Theorem: QWEN-CODER-7B-UPGRADE-CONDITIONS-PASS.

    If wave-5's K-widening sweep returns an F_eff ≥ 950 perthou
    (≥ 0.95), the post-wave-5 status of Qwen-Coder-7B is
    `Certified`. -/
theorem qwen_coder_7b_upgrade_conditions_pass
    (r : WaveFiveSweepResult)
    (h : r.best_F_perthou ≥ wave_5_pass_threshold_perthou) :
    qwen_coder_7b_status_after_wave_5 r = .Certified := by
  unfold qwen_coder_7b_status_after_wave_5
  unfold wave_5_clears_threshold
  simp [h]

/-- Theorem: QWEN-CODER-7B-UPGRADE-CONDITIONS-FAIL.

    If wave-5's sweep falls SHORT of the 950 perthou threshold,
    the post-wave-5 status of Qwen-Coder-7B is
    `DemotedAfterMeasurement`. The wave-3 RuntimeCertificate
    definition must then be revised to use the measured F=0
    instead of the projected F=40/100 (see the doc-comment at
    top of file for the operational follow-up). -/
theorem qwen_coder_7b_upgrade_conditions_fail
    (r : WaveFiveSweepResult)
    (h : r.best_F_perthou < wave_5_pass_threshold_perthou) :
    qwen_coder_7b_status_after_wave_5 r = .DemotedAfterMeasurement := by
  unfold qwen_coder_7b_status_after_wave_5
  unfold wave_5_clears_threshold
  have hnot : ¬ (r.best_F_perthou ≥ wave_5_pass_threshold_perthou) :=
    Nat.not_le_of_lt h
  simp [hnot]

/-- Theorem: QWEN-CODER-7B-UPGRADE-IS-DICHOTOMY.

    The post-wave-5 status of Qwen-Coder-7B is exactly one of
    `Certified` or `DemotedAfterMeasurement` — there is no third
    option, no "still ProjectedCertified" loophole. The ledger
    forces the measurement to land before the model is shipped
    again. -/
theorem qwen_coder_7b_upgrade_is_dichotomy (r : WaveFiveSweepResult) :
    qwen_coder_7b_status_after_wave_5 r = .Certified ∨
    qwen_coder_7b_status_after_wave_5 r = .DemotedAfterMeasurement := by
  unfold qwen_coder_7b_status_after_wave_5
  by_cases h : wave_5_clears_threshold r = true
  · left;  simp [h]
  · right; simp [h]

-- ══════════════════════════════════════════════════════════
-- LEDGER-LEVEL SANITY (the demotion is not vacuous)
-- ══════════════════════════════════════════════════════════

/-- Theorem: LEDGER-CONTAINS-A-DEMOTION.

    The post-wave-4 ledger has at least one model in the
    `DemotedAfterMeasurement` state. The witness is
    Qwen-Coder-7B. This is the formal anti-vacuity check on the
    whole record: the demotion enum is not just defined, it is
    actually used. -/
theorem ledger_contains_a_demotion :
    ∃ m : ModelId,
      current_certification_status m = .DemotedAfterMeasurement := by
  exact ⟨.qwen_coder_7b, qwen_coder_7b_demoted_after_wave_4_measurement⟩

/-- Theorem: LEDGER-CONTAINS-A-MEASURED-CERTIFIED.

    Even after the demotion the ledger still has at least one
    model in the fully `Certified` state. Witness: Qwen2.5-0.5B.
    The deployment story does not collapse because of one
    falsified projection — it just stops claiming what it has
    not measured. -/
theorem ledger_contains_a_measured_certified :
    ∃ m : ModelId, current_certification_status m = .Certified := by
  exact ⟨.qwen_0_5b, qwen_0_5b_remains_certified⟩

/-- Theorem: LEDGER-CONTAINS-A-PENDING-PROJECTION.

    The ledger still records at least one `ProjectedCertified`
    entry: Llama-1B. Wave-5 (or later) must run the parity
    pipeline on it and resolve it the same way wave-4 resolved
    Qwen-Coder-7B. -/
theorem ledger_contains_a_pending_projection :
    ∃ m : ModelId, current_certification_status m = .ProjectedCertified := by
  exact ⟨.llama_1b, llama_1b_projection_pending_measurement⟩

end CertificationDemotion
end Gnosis
