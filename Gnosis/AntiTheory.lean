import Gnosis.CrossModelOperationalGap
import Gnosis.SpecDecodeKDependence
import Gnosis.CertificationDemotion

/-
  AntiTheory.lean
  ===============

  THE ANTI-THEORY CORE.

  After three cumulative empirical falsifications across waves 4, 5, and
  6, the Theory of Model Physics no longer presents itself as a single
  layer of "claims that hold". The honest structure has split in two:

    • STRUCTURAL LAYER. Identities proved BY CONSTRUCTION in Lean.
      These are not falsifiable by measurement; they hold or fail to
      hold formally. Examples in this codebase: the
      CompressionUncertainty principle and the Novikov closure
      identity. They are theorems, not predictions.

    • EMPIRICAL LAYER. Claims that specify their own FALSIFYING
      EXPERIMENT. Default status is `NotYetFalsified`. Only
      methodology-pinned, measured claims participate in the
      falsification ledger; an unmethologized claim is recorded as
      `VacuousNoExperimentSpecified`.

  The Theory's scientific content is therefore:

    1. The set of structural identities (proved or disproved formally),
       PLUS
    2. The falsification ledger: the list of measured falsifications
       (permanent) and the list of `NotYetFalsified` conjectures, EACH
       with the experiment that would falsify it.

  Three permanent falsifications are recorded here:

    F1. Cross-model PCA-only at K=5 does NOT transfer (qwen-0.5b
        certifies, qwen-coder-7b does not). Source:
        `CrossModelOperationalGap`.

    F2. Strict K=1 speculative decoding on PCA-only drafts achieves
        zero accept rate at N=2, 4, 8. Source:
        `SpecDecodeKDependence`.

    F3. The k/hidden_dim ratio is NOT a methodology-independent
        invariant; rank density depends on the measurement
        protocol. Source: `CertificationDemotion`.

  This module is the LOAD-BEARING ANCHOR of the Anti-Theory turn. Its
  load-bearing inversion is on the DEFAULT: an empirical claim with
  no specified falsifying experiment is `VacuousNoExperimentSpecified`,
  not "true until refuted". Falsifications are first-class and
  permanent; conjectures are provisional and revocable.

  Init-only Lean 4. Zero sorries, zero axioms.
-/


namespace Gnosis
namespace AntiTheory

-- ══════════════════════════════════════════════════════════
-- THE FOUR EMPIRICAL CLAIM STATES
-- ══════════════════════════════════════════════════════════

/-- The status of an empirical claim under the Anti-Theory turn.

    These are NOT a quality ranking. They are the four distinct
    epistemic states an empirical claim can be in once one asks
    "what would falsify this?".

    • `NotYetFalsified` — the only honest default for a methodology-
      pinned claim that has been measured and not refuted. NOT
      "true"; merely "consistent with the measurements taken so far".

    • `FalsifiedByMeasurement` — at least one measurement has refuted
      the claim. PERMANENT. The Anti-Theory turn does not allow
      measured falsifications to be revoked; new conjectures may be
      formed, but the historical falsification stays on the ledger.

    • `StructuralIdentity` — the claim is NOT empirical. It is proved
      by construction (a Lean theorem). Status `StructuralIdentity`
      means "do not ask for a falsifying experiment; ask for the
      proof". Examples elsewhere in this codebase: CompressionUncertainty,
      Novikov closure.

    • `VacuousNoExperimentSpecified` — the claim does not pin its
      methodology. It cannot in principle be falsified; therefore it
      contributes nothing to the falsification ledger and is recorded
      here as vacuous. THIS IS THE LOAD-BEARING DEFAULT-INVERSION:
      a claim without a specified falsifying experiment is not
      "interesting until disproved" — it is vacuous from the start. -/
inductive EmpiricalClaimStatus
  | NotYetFalsified
  | FalsifiedByMeasurement
  | StructuralIdentity
  | VacuousNoExperimentSpecified
  deriving DecidableEq, Repr

-- ══════════════════════════════════════════════════════════
-- THE FALSIFYING-EXPERIMENT RECORD
-- ══════════════════════════════════════════════════════════

/-- The bookkeeping record of a single empirical claim and the
    experiment that would falsify it.

    Fields:
      • `hypothesis_text`     — informal statement of the claim
        (kept as a String so the ledger reads as a document, not
        a code lookup).
      • `methodology_pinned`  — does the claim specify its
        measurement protocol? If false, the claim cannot in
        principle be falsified and is therefore vacuous.
      • `witness_count`       — how many measured instances are
        consistent with the claim (NOT a proof; merely a tally).
      • `counterexamples`     — how many measurements REFUTE the
        claim. One is enough; the count is preserved for the
        ledger. -/
structure FalsifyingExperiment where
  hypothesis_text     : String
  methodology_pinned  : Bool
  witness_count       : Nat
  counterexamples     : Nat
  deriving Repr

-- ══════════════════════════════════════════════════════════
-- THE MEANINGFULNESS PREDICATE
-- ══════════════════════════════════════════════════════════

/-- An empirical claim is SCIENTIFICALLY MEANINGFUL iff:

      (a) it pins its methodology (so it CAN be falsified), AND
      (b) at least one measurement has actually been taken
          (witnesses or counterexamples > 0).

    Pinning a methodology without measuring is a promise; measuring
    without pinning is incoherent. Both pieces are required before
    the claim earns a place on the ledger. -/
def is_scientifically_meaningful (e : FalsifyingExperiment) : Bool :=
  e.methodology_pinned && decide (e.witness_count + e.counterexamples > 0)

-- ══════════════════════════════════════════════════════════
-- THE STATUS FUNCTION
-- ══════════════════════════════════════════════════════════

/-- Compute the current status of an empirical claim from its
    `FalsifyingExperiment` record.

    Three branches, in order:

      1. If the methodology is NOT pinned, the claim is
         `VacuousNoExperimentSpecified`. (Default-inversion.)

      2. Otherwise, if at least one counterexample has been
         measured, the claim is `FalsifiedByMeasurement`.
         Permanent.

      3. Otherwise (methodology pinned, zero counterexamples),
         the claim is `NotYetFalsified`. Note: this branch is
         agnostic about whether any witnesses have been measured;
         a methodology-pinned claim with zero observations is
         `NotYetFalsified` in the literal sense — it has not
         yet been falsified, because it has not yet been tested.
         The `is_scientifically_meaningful` predicate filters
         that case out separately. -/
def current_status (e : FalsifyingExperiment) : EmpiricalClaimStatus :=
  if !e.methodology_pinned then
    .VacuousNoExperimentSpecified
  else if e.counterexamples > 0 then
    .FalsifiedByMeasurement
  else
    .NotYetFalsified

-- ══════════════════════════════════════════════════════════
-- THE THREE PERMANENT FALSIFICATIONS (waves 4-6)
-- ══════════════════════════════════════════════════════════

/-- F1. Cross-model PCA-only at K=5 transfers across same-family
    scale-up.

    Methodology: run the wave-1 PCA-only standing-wave-pinning
    picker at fixed K=5 against the cliff-band layers, on a
    next-larger same-family model, and measure F_eff.

    Witnesses:    1  (Qwen2.5-0.5B at K=5: F_eff = 1.00).
    Counterexamples: 1 (Qwen-Coder-7B at K=5: F_eff = 0.00).

    See `Gnosis.CrossModelOperationalGap` for the per-instance
    `OperationalReading`s and the decoupling theorem. -/
def f1_cross_model_pca_at_K5 : FalsifyingExperiment :=
  { hypothesis_text     :=
      "PCA-only cliff prediction transfers across model scale at K=5"
  , methodology_pinned  := true
  , witness_count       := 1
  , counterexamples     := 1 }

/-- F2. Strict K=1 speculative decoding preserves argmax under a
    PCA-only draft.

    Methodology: run speculative decoding with strict K=1 (per-position
    argmax matching) using the PCA-only draft scheme, and measure
    accept rate over a fixed N-token window.

    Witnesses:    0.
    Counterexamples: 3 (N=2, N=4, N=8 — all measured 0/1000 accept
    rate, with wall-clock slowdowns of 4x, 8x, 16x respectively).

    See `Gnosis.SpecDecodeKDependence` for the per-instance
    `KFidelityReading`s. -/
def f2_strict_K1_spec_decode_on_PCA : FalsifyingExperiment :=
  { hypothesis_text     :=
      "K=1 spec-decode preserves argmax under PCA-only"
  , methodology_pinned  := true
  , witness_count       := 0
  , counterexamples     := 3 }

/-- F3. The ratio k / hidden_dim is the methodology-independent
    invariant for compressibility.

    Methodology: across at least two distinct measurement protocols
    (e.g. PCA-only standing-wave pinning vs. K-set speculative
    decoding), the rank density k/hidden_dim should yield the same
    operational verdict on the same model.

    Witnesses:    1  (the wave-1/2 PCA-K=8 pinning on Qwen2.5-0.5B
                      gave k/d ≈ 8/896, certified).
    Counterexamples: 1 (the same k/d ratio scaled to Qwen-Coder-7B
                        gave 32/3584 — not certified at the
                        operational K=5 measurement, and the
                        certification verdict shifted with
                        protocol).

    See `Gnosis.CertificationDemotion` for the demotion ledger. -/
def f3_rank_density_invariant : FalsifyingExperiment :=
  { hypothesis_text     :=
      "k/hidden_dim ratio is the methodology-independent invariant"
  , methodology_pinned  := true
  , witness_count       := 1
  , counterexamples     := 1 }

-- ══════════════════════════════════════════════════════════
-- PER-INSTANCE FALSIFICATION VERDICTS (decide-checked)
-- ══════════════════════════════════════════════════════════

/-- F1's status is `FalsifiedByMeasurement`. Permanent. -/
theorem f1_status_is_falsified :
    current_status f1_cross_model_pca_at_K5
      = EmpiricalClaimStatus.FalsifiedByMeasurement := by
  decide

/-- F2's status is `FalsifiedByMeasurement`. Permanent. -/
theorem f2_status_is_falsified :
    current_status f2_strict_K1_spec_decode_on_PCA
      = EmpiricalClaimStatus.FalsifiedByMeasurement := by
  decide

/-- F3's status is `FalsifiedByMeasurement`. Permanent. -/
theorem f3_status_is_falsified :
    current_status f3_rank_density_invariant
      = EmpiricalClaimStatus.FalsifiedByMeasurement := by
  decide

/-- All three falsifications are scientifically meaningful: each
    pins its methodology AND has been measured (witnesses or
    counterexamples > 0). -/
theorem all_three_falsifications_are_scientifically_meaningful :
    is_scientifically_meaningful f1_cross_model_pca_at_K5 = true ∧
    is_scientifically_meaningful f2_strict_K1_spec_decode_on_PCA = true ∧
    is_scientifically_meaningful f3_rank_density_invariant = true := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- THE LOAD-BEARING DEFAULT-INVERSION
-- ══════════════════════════════════════════════════════════

/-- THE LOAD-BEARING INVERSION.

    For ANY `FalsifyingExperiment` whose `methodology_pinned`
    field is `false`, `current_status` returns
    `VacuousNoExperimentSpecified` — regardless of how many
    "witnesses" the claim accumulates.

    This is the Anti-Theory turn made formal. The default state
    of an unmethologized empirical claim is not "true until
    refuted". It is vacuous from the start, and it does not
    earn a slot on the falsification ledger.

    The proof is by `cases` on `methodology_pinned`; the `false`
    case discharges by definitional reduction of `current_status`. -/
theorem unmethologized_claim_is_vacuous
    (e : FalsifyingExperiment) (h : e.methodology_pinned = false) :
    current_status e = EmpiricalClaimStatus.VacuousNoExperimentSpecified := by
  unfold current_status
  rw [h]
  rfl

-- ══════════════════════════════════════════════════════════
-- THE STRUCTURAL LAYER
-- ══════════════════════════════════════════════════════════

/-- A structural-identity claim. UNLIKE a `FalsifyingExperiment`,
    this carries no `methodology_pinned` / `witnesses` /
    `counterexamples` fields. The right question for a structural
    identity is NOT "what would falsify it?" — it is "what is the
    proof?".

    Field:
      • `claim_text` — informal statement of the identity.

    By convention in this module, `current_status` of a
    `StructuralIdentityClaim` is the constant
    `EmpiricalClaimStatus.StructuralIdentity`. -/
structure StructuralIdentityClaim where
  claim_text : String
  deriving Repr

/-- The status of a structural identity is, by definition,
    `StructuralIdentity`. The function is constant; the structure
    of `StructuralIdentityClaim` carries no field that could move
    its status to `FalsifiedByMeasurement`. -/
def structural_status (_ : StructuralIdentityClaim) : EmpiricalClaimStatus :=
  .StructuralIdentity

/-- The CompressionUncertainty principle is a STRUCTURAL identity.
    It is proved by construction in `Gnosis.CompressionUncertainty`;
    it does not get falsified by a measurement. -/
def compression_uncertainty_principle_is_structural :
    StructuralIdentityClaim :=
  { claim_text :=
      "CompressionUncertainty: ΔK · ΔF ≥ c, proved by construction" }

/-- The Novikov closure identity is a STRUCTURAL identity. It is
    proved by construction; it does not get falsified by a
    measurement. -/
def novikov_closure_is_structural : StructuralIdentityClaim :=
  { claim_text :=
      "Novikov closure: self-consistent histories close under composition" }

-- ══════════════════════════════════════════════════════════
-- THE TWO-LAYER SEPARATION THEOREM
-- ══════════════════════════════════════════════════════════

/-- Theorem: STRUCTURAL-IDENTITIES-ARE-NOT-FALSIFIABLE-IN-THE-
              EMPIRICAL-SENSE.

    For ANY `StructuralIdentityClaim`, `structural_status`
    returns `StructuralIdentity`, which is DISTINCT from
    `FalsifiedByMeasurement` at the type level. Therefore no
    structural identity ever has status `FalsifiedByMeasurement`.

    This is the formal expression of the two-layer split: an
    object of type `StructuralIdentityClaim` cannot, in
    principle, end up with the `FalsifiedByMeasurement` tag. The
    only way a structural identity changes status is by changing
    its proof — i.e. by working in the structural layer, not in
    the empirical one. -/
theorem structural_identities_are_not_falsifiable_in_the_empirical_sense
    (s : StructuralIdentityClaim) :
    structural_status s ≠ EmpiricalClaimStatus.FalsifiedByMeasurement := by
  unfold structural_status
  decide

/-- Companion theorem: the two specific structural identities
    pinned in this module both have `structural_status` equal to
    `StructuralIdentity`. Decided pointwise. -/
theorem named_structural_identities_have_structural_status :
    structural_status compression_uncertainty_principle_is_structural
      = EmpiricalClaimStatus.StructuralIdentity ∧
    structural_status novikov_closure_is_structural
      = EmpiricalClaimStatus.StructuralIdentity := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

-- ══════════════════════════════════════════════════════════
-- TIE-BACKS TO THE THREE WAVE MODULES
-- ══════════════════════════════════════════════════════════

/-- Tie-back: F1's empirical content is exactly the
    `structural_prediction_does_not_transfer_at_fixed_K` theorem
    in `CrossModelOperationalGap`. The `FalsifyingExperiment`
    record here is the ledger entry; the witness lives there. -/
theorem f1_ties_back_to_cross_model_operational_gap :
    current_status f1_cross_model_pca_at_K5
      = EmpiricalClaimStatus.FalsifiedByMeasurement ∧
    Gnosis.CrossModelOperationalGap.is_operationally_certified
      Gnosis.CrossModelOperationalGap.qwen_coder_7b_K5_pca_operational
      = false := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

/-- Tie-back: F3's empirical content is the wave-3 → wave-4
    demotion recorded in `CertificationDemotion`. Qwen-Coder-7B
    sits at `DemotedAfterMeasurement` in that module's status
    function; here it appears as a counterexample on the
    rank-density-invariant ledger. -/
theorem f3_ties_back_to_certification_demotion :
    current_status f3_rank_density_invariant
      = EmpiricalClaimStatus.FalsifiedByMeasurement ∧
    Gnosis.CertificationDemotion.current_certification_status
      Gnosis.CertificationDemotion.ModelId.qwen_coder_7b
      = Gnosis.CertificationDemotion.CertificationStatus.DemotedAfterMeasurement
    := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

end AntiTheory
end Gnosis
