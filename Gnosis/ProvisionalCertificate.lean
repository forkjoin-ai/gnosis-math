/-
  ProvisionalCertificate.lean
  ===========================

  THE ANTI-THEORY REPLACEMENT FOR `Certified`.

  This module replaces `MultiModelCertificateAtlas`'s `Certified`
  constructor with the anti-theory equivalent:
  `NotYetFalsifiedUnder methodology witnesses`.

  The "Certified" claim was vacuous — it asserted a property without
  specifying the falsifying experiment. Anti-theory inverts this: the
  default is "we have not yet falsified this under methodology M with
  N witnesses." A claim becomes interesting only after you can name
  the experiment that would refute it AND that experiment has at least
  one supporting witness AND zero falsifying witnesses on record.

  Three current statuses (state as of 2026-05-03, post-wave-4):

    • qwen-0.5b       — NotYetFalsified
                        (one supporting witness, the wave-2 K=8 measurement)

    • qwen-coder-7b   — FalsifiedByMeasurement
                        (one falsifying witness, the wave-4 K=5 PCA-only run
                         that returned F=0/30)

    • llama-1b        — VacuousNoExperimentSpecified
                        (no measurements at all — wave-3 PROJECTED a number
                         from the qwen-0.5b sibling and called the result
                         "ProjectedCertified". Anti-theory marks this as
                         the most honest correction in the ledger: a
                         never-measured projection is not a certificate
                         of any kind. It is a vacuous claim awaiting its
                         falsifying experiment.)

  We do NOT edit `MultiModelCertificateAtlas.lean`. That module stays
  as the historical pre-anti-theory record of what wave-3 CLAIMED to
  have certified. This module is the CORRECTION ledger, written from
  the post-anti-theory standpoint.

  Init-only Lean 4. Zero sorries, zero axioms.
-/

namespace Gnosis
namespace ProvisionalCertificate

-- ══════════════════════════════════════════════════════════
-- THE THREE EMPIRICAL CLAIM STATUSES
-- ══════════════════════════════════════════════════════════

/-- The three epistemic states that an empirical claim can be in
    under the anti-theory regime.

    • `NotYetFalsified`              — the claim has at least one
      supporting witness and zero falsifying witnesses. It is alive
      and on probation. NOT a certificate of truth.

    • `FalsifiedByMeasurement`       — the claim has at least one
      falsifying witness. The hypothesis is dead at the recorded
      methodology. (A K-widening sweep may still rescue a related
      hypothesis at a different K, but THIS hypothesis is done.)

    • `VacuousNoExperimentSpecified` — the claim has zero supporting
      witnesses and zero falsifying witnesses. It is not even
      meaningful: nobody has run the experiment. The wave-3 atlas
      called this "ProjectedCertified". Anti-theory calls it for
      what it is: vacuous. -/
inductive EmpiricalClaimStatus
  | NotYetFalsified
  | FalsifiedByMeasurement
  | VacuousNoExperimentSpecified
  deriving DecidableEq, Repr

-- ══════════════════════════════════════════════════════════
-- THE THREE WAVE-3 ATLAS MODELS (re-declared symbolically)
-- ══════════════════════════════════════════════════════════

/-- Stable identifiers for the three models the wave-3 atlas
    declared. Re-declared inline so this module compiles standalone
    without importing the wave-2/3 numeric bundles (those are still
    accessible via `Gnosis.CertificationDemotion`, but we keep the
    anti-theory record orthogonal to the demotion ledger). -/
inductive ModelId
  | Qwen0_5B
  | QwenCoder7B
  | Llama1B
  deriving DecidableEq, Repr

-- ══════════════════════════════════════════════════════════
-- METHODOLOGY WITNESS
-- ══════════════════════════════════════════════════════════

/-- A single methodology witness: the concrete experimental
    configuration that produced one supporting-or-falsifying
    measurement against an empirical claim.

    All numeric fields are Nat in canonical units so the structure
    is decide-friendly (no Rat, no Float).

    • `probe_coverage_perthou`    — coverage in parts per thousand
      (0.50 ⇒ 500). The fraction of probe positions exercised in
      the parity sweep.

    • `cal_token_count`           — number of tokens in the
      calibration window.

    • `test_token_count`          — number of tokens in the held-out
      test window the witness was scored on.

    • `candidate_K`               — the K-value (number of
      candidate residual modes) used by the standing-wave PCA
      head. Wave-2 measured K=8 on qwen-0.5b. Wave-4 measured K=5
      on qwen-coder-7b.

    • `measured_cosine_perthou`   — measured cosine similarity in
      parts per thousand (0.95 ⇒ 950, 1.00 ⇒ 1000, 0.00 ⇒ 0).
      This is THE outcome number.

    • `measured_in_wave`          — which wave produced this
      witness. 1=wave-1, 2=wave-2, etc. -/
structure MethodologyWitness where
  probe_coverage_perthou  : Nat
  cal_token_count         : Nat
  test_token_count        : Nat
  candidate_K             : Nat
  measured_cosine_perthou : Nat
  measured_in_wave        : Nat
  deriving Repr

-- ══════════════════════════════════════════════════════════
-- PROVISIONAL CERTIFICATE
-- ══════════════════════════════════════════════════════════

/-- A provisional certificate: the anti-theory replacement for the
    old `Certified` constructor.

    A provisional certificate names:

      1. The model under test.
      2. The hypothesis being asserted (as a free-form String — the
         English statement the operator is willing to be wrong about).
      3. The list of supporting witnesses (measurements that DID NOT
         falsify the hypothesis).
      4. The list of falsifying witnesses (measurements that DID
         falsify the hypothesis).

    The current status is read off via
    `current_provisional_status` below — it is NOT stored, because
    the status is a function of the witness lists and storing it
    would let the two drift. -/
structure ProvisionalCertificate where
  model_id              : ModelId
  hypothesis            : String
  witnesses_supporting  : List MethodologyWitness
  witnesses_falsifying  : List MethodologyWitness
  deriving Repr

-- ══════════════════════════════════════════════════════════
-- CURRENT-STATUS READOUT
-- ══════════════════════════════════════════════════════════

/-- Read the current empirical-claim status off a provisional
    certificate.

    Decision tree (in order, first match wins):

      1. If there is at least one falsifying witness ⇒
         `FalsifiedByMeasurement`. (One falsifying measurement
         kills the hypothesis at the recorded methodology.)

      2. Else if there are zero supporting witnesses ⇒
         `VacuousNoExperimentSpecified`. (No experiment has been
         run; the claim is not yet meaningful.)

      3. Else ⇒ `NotYetFalsified`. (At least one supporting
         witness, no falsifying witnesses. Alive and on probation.)

    Note that `NotYetFalsified` is NOT `Certified`. It is the
    weakest possible positive status: "we tried to break it and
    didn't, so far, with the witnesses on file." -/
def current_provisional_status (c : ProvisionalCertificate) :
    EmpiricalClaimStatus :=
  if c.witnesses_falsifying.length > 0 then
    .FalsifiedByMeasurement
  else if c.witnesses_supporting.length = 0 then
    .VacuousNoExperimentSpecified
  else
    .NotYetFalsified

-- ══════════════════════════════════════════════════════════
-- PER-MODEL WITNESSES (the actual measurements on file)
-- ══════════════════════════════════════════════════════════

/-- Wave-2 supporting witness for Qwen2.5-0.5B: the K=8 PCA-only
    measurement that returned cosine = 1.000 (1000 perthou). This
    is the original wave-2 RuntimeCertificate measurement, encoded
    here in the anti-theory schema. -/
def wave_2_qwen_0_5b_supporting_witness : MethodologyWitness :=
  { probe_coverage_perthou  := 500   -- 0.50 coverage
  , cal_token_count         := 100
  , test_token_count        := 100
  , candidate_K             := 8
  , measured_cosine_perthou := 1000  -- cosine = 1.000
  , measured_in_wave        := 2 }

/-- Wave-4 falsifying witness for Qwen-Coder-7B: the K=5 PCA-only
    measurement at coverage 0.50 that returned cosine = 0.000
    (0 perthou). This is the wave-4 measurement that demoted the
    wave-3 projection. Encoded here in the anti-theory schema. -/
def wave_4_qwen_coder_7b_falsifying_witness : MethodologyWitness :=
  { probe_coverage_perthou  := 500   -- 0.50 coverage
  , cal_token_count         := 30
  , test_token_count        := 30
  , candidate_K             := 5
  , measured_cosine_perthou := 0     -- cosine = 0.000  (the killer)
  , measured_in_wave        := 4 }

-- ══════════════════════════════════════════════════════════
-- THE THREE PER-MODEL PROVISIONAL CERTIFICATES
-- ══════════════════════════════════════════════════════════

/-- Qwen2.5-0.5B's anti-theory provisional certificate.

    Hypothesis: "PCA-only at k=8, K=5, coverage=0.50 achieves
    cosine ≥ 0.95". One supporting witness (the wave-2 K=8 measurement
    at cosine=1.000). Zero falsifying witnesses. Status:
    `NotYetFalsified`. -/
def qwen_0_5b_prov_cert : ProvisionalCertificate :=
  { model_id              := .Qwen0_5B
  , hypothesis            :=
      "PCA-only at k=8, K=5, coverage=0.50 achieves cosine ≥ 0.95"
  , witnesses_supporting  := [wave_2_qwen_0_5b_supporting_witness]
  , witnesses_falsifying  := [] }

/-- Qwen-Coder-7B's anti-theory provisional certificate.

    Hypothesis: same as qwen-0.5b. Zero supporting witnesses (the
    wave-3 "support" was a projection, not a measurement, so it does
    not count). One falsifying witness (the wave-4 K=5 PCA-only run
    at cosine=0.000). Status: `FalsifiedByMeasurement`. -/
def qwen_coder_7b_prov_cert : ProvisionalCertificate :=
  { model_id              := .QwenCoder7B
  , hypothesis            :=
      "PCA-only at k=8, K=5, coverage=0.50 achieves cosine ≥ 0.95"
  , witnesses_supporting  := []
  , witnesses_falsifying  := [wave_4_qwen_coder_7b_falsifying_witness] }

/-- Llama-1B's anti-theory provisional certificate.

    Hypothesis: same as qwen-0.5b. Zero supporting witnesses, zero
    falsifying witnesses — Llama-1B was NEVER MEASURED. Wave-3
    called this "ProjectedCertified". Anti-theory calls it for what
    it is: `VacuousNoExperimentSpecified`.

    THE LOAD-BEARING CORRECTION. The wave-3 ledger conflated "we
    haven't measured this yet" with "we measured this and it was
    fine." Anti-theory refuses that conflation. Until somebody runs
    the parity pipeline on llama-1b, there is no claim here at all
    — only a hypothesis awaiting its first witness, supporting or
    falsifying. -/
def llama_1b_prov_cert : ProvisionalCertificate :=
  { model_id              := .Llama1B
  , hypothesis            :=
      "PCA-only at k=8, K=5, coverage=0.50 achieves cosine ≥ 0.95"
  , witnesses_supporting  := []
  , witnesses_falsifying  := [] }

-- ══════════════════════════════════════════════════════════
-- PER-INSTANCE STATUS THEOREMS (decide-checked)
-- ══════════════════════════════════════════════════════════

/-- Theorem: QWEN-0.5B IS NOT-YET-FALSIFIED.

    The wave-2 K=8 measurement at cosine=1.000 is a supporting
    witness; no falsifying witness is on file. The hypothesis is
    alive on probation. Anti-theory does NOT promote this to a
    certificate of truth. -/
theorem qwen_0_5b_is_NotYetFalsified :
    current_provisional_status qwen_0_5b_prov_cert
      = .NotYetFalsified := by
  decide

/-- Theorem: QWEN-CODER-7B IS FALSIFIED-BY-MEASUREMENT.

    The wave-4 K=5 PCA-only run at coverage=0.50 measured
    cosine=0.000. That single falsifying witness kills the
    hypothesis at the recorded methodology. -/
theorem qwen_coder_7b_is_FalsifiedByMeasurement :
    current_provisional_status qwen_coder_7b_prov_cert
      = .FalsifiedByMeasurement := by
  decide

/-- Theorem: LLAMA-1B IS VACUOUS-NO-EXPERIMENT-SPECIFIED.

    THE LOAD-BEARING CORRECTION TO WAVE-3. The wave-3 atlas listed
    Llama-1B as "ProjectedCertified" — a status that conflated "we
    have not measured this" with "we have measured this and it was
    fine." Anti-theory rejects that conflation: zero supporting and
    zero falsifying witnesses ⇒ `VacuousNoExperimentSpecified`. The
    claim is not yet meaningful and must not be treated as one. -/
theorem llama_1b_is_VacuousNoExperimentSpecified :
    current_provisional_status llama_1b_prov_cert
      = .VacuousNoExperimentSpecified := by
  decide

-- ══════════════════════════════════════════════════════════
-- LEDGER-LEVEL CORRECTNESS THEOREMS
-- ══════════════════════════════════════════════════════════

/-- Theorem: PREVIOUSLY-CERTIFIED MODELS ARE NOW EITHER PROVISIONAL
    OR FALSIFIED.

    No model in the post-anti-theory ledger has the old "Certified"
    status. Every entry is either `NotYetFalsified` (alive on
    probation), `FalsifiedByMeasurement` (dead at the recorded
    methodology), or `VacuousNoExperimentSpecified` (not yet a
    claim). We exhibit this for all three wave-3 atlas entries. -/
theorem previously_certified_models_are_now_either_provisional_or_falsified :
    (current_provisional_status qwen_0_5b_prov_cert
       = .NotYetFalsified ∨
     current_provisional_status qwen_0_5b_prov_cert
       = .FalsifiedByMeasurement ∨
     current_provisional_status qwen_0_5b_prov_cert
       = .VacuousNoExperimentSpecified) ∧
    (current_provisional_status qwen_coder_7b_prov_cert
       = .NotYetFalsified ∨
     current_provisional_status qwen_coder_7b_prov_cert
       = .FalsifiedByMeasurement ∨
     current_provisional_status qwen_coder_7b_prov_cert
       = .VacuousNoExperimentSpecified) ∧
    (current_provisional_status llama_1b_prov_cert
       = .NotYetFalsified ∨
     current_provisional_status llama_1b_prov_cert
       = .FalsifiedByMeasurement ∨
     current_provisional_status llama_1b_prov_cert
       = .VacuousNoExperimentSpecified) := by
  decide

-- ══════════════════════════════════════════════════════════
-- THE HONESTY THEOREM
-- ══════════════════════════════════════════════════════════

/-- Theorem: VACUOUS-STATUS IS NOT NotYetFalsified.

    The honesty theorem. Distinguishing "we haven't measured this"
    (`VacuousNoExperimentSpecified`) from "we've measured this and
    not falsified it" (`NotYetFalsified`) is LOAD-BEARING. The
    previous certificate atlas conflated these two and labelled
    Llama-1B as "ProjectedCertified", treating an unmeasured
    projection as if it were a passing test.

    Anti-theory makes the distinction proof-checked: the two
    statuses are constructor-level distinct. There is no path by
    which a vacuous claim can be read as a not-yet-falsified
    claim. -/
theorem vacuous_status_is_NOT_NotYetFalsified :
    EmpiricalClaimStatus.VacuousNoExperimentSpecified
      ≠ EmpiricalClaimStatus.NotYetFalsified := by
  decide

-- ══════════════════════════════════════════════════════════
-- CLI-STYLE SUMMARY REPORT
-- ══════════════════════════════════════════════════════════

/-- Render a single `EmpiricalClaimStatus` as a short string. -/
def statusToString : EmpiricalClaimStatus → String
  | .NotYetFalsified              => "NotYetFalsified"
  | .FalsifiedByMeasurement       => "FalsifiedByMeasurement"
  | .VacuousNoExperimentSpecified => "VacuousNoExperimentSpecified"

/-- Render a single `ModelId` as the operator-facing model name. -/
def modelIdToString : ModelId → String
  | .Qwen0_5B    => "qwen-0.5b"
  | .QwenCoder7B => "qwen-coder-7b"
  | .Llama1B     => "llama-1b"

/-- Render one provisional certificate as a CLI-style summary line:

      "MODEL_ID: STATUS, n_supporting=K, n_falsifying=M, hypothesis=H"

    Used by future agents to dump the current state of the
    provisional-certificate ledger. -/
def summarizeOne (c : ProvisionalCertificate) : String :=
  modelIdToString c.model_id ++ ": " ++
  statusToString (current_provisional_status c) ++
  ", n_supporting=" ++ toString c.witnesses_supporting.length ++
  ", n_falsifying=" ++ toString c.witnesses_falsifying.length ++
  ", hypothesis=" ++ c.hypothesis

/-- CLI-style summary report. Renders a list of provisional
    certificates as one summary line per certificate, joined by
    newlines.

    Example call:

      summarize
        [ qwen_0_5b_prov_cert
        , qwen_coder_7b_prov_cert
        , llama_1b_prov_cert ]

    yields three lines, one per model, suitable for piping into
    a log file or rendering into a status page. -/
def summarize (cs : List ProvisionalCertificate) : String :=
  String.intercalate "\n" (cs.map summarizeOne)

/-- The canonical post-wave-4 ledger: all three wave-3 atlas
    models, in canonical order. -/
def current_ledger : List ProvisionalCertificate :=
  [ qwen_0_5b_prov_cert
  , qwen_coder_7b_prov_cert
  , llama_1b_prov_cert ]

end ProvisionalCertificate
end Gnosis
