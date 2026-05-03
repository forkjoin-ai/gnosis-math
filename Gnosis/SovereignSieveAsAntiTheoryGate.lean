/-
  SovereignSieveAsAntiTheoryGate.lean
  ===================================

  THE SOVEREIGN SIEVE AS ANTI-THEORY'S OPERATIONAL ENFORCER.

  The structural Lean modules formalize WHAT anti-theory is. This
  module formalizes HOW anti-theory is enforced at runtime: the
  SOVEREIGN SIEVE is the gate that admits, rejects, or defers each
  `FalsifyingExperiment` based on three load-bearing checks:

    (a) METHODOLOGY PINNING — the anti-theory directive. A claim
        without a pinned methodology cannot in principle be
        falsified; the sieve REJECTS it from production. The
        wave-3 `ProjectedCertified` mistakes (qwen-coder-7b /
        llama-1b at k=8 PCA-only) had `methodology_pinned = false`
        and would have been rejected by a default sovereign sieve
        BEFORE the wave-4 falsification embarrassment.

    (b) BULE BUDGET — the no-cloning tax. A claim cannot enter
        production for free; admission ALWAYS costs at least
        `operational_threshold_bule` measurement witnesses. The
        sieve refuses to clone vacuous claims into the deployment
        ledger without a positive bule payment. This mirrors
        `Gnosis.NoCloningTaxEqualsBuleCost` operationally:
        admission costs bule, never zero.

    (c) COUNTEREXAMPLE COUNT — the falsification rejection. A
        claim with even one measured counterexample is
        `FalsifiedByMeasurement` and the sieve REJECTS it. F1, F2,
        F3, F4, F5 all have `counterexamples > 0` and are all
        rejected uniformly — the sovereign sieve is the runtime's
        first line of defense against shipping refuted claims.

  Three decisions, three values:

    • `Admit`  — methodology pinned, bule paid, no counterexamples.
                 The claim crosses the gate into production.
    • `Reject` — methodology missing OR counterexamples present.
                 The claim cannot enter production.
    • `Defer`  — methodology pinned, no counterexamples, but bule
                 budget unmet. The claim sits in queue until enough
                 measurements arrive to clear the threshold.

  ----------------------------------------------------------------
  WAVE-3 / WAVE-15 IMPLICATIONS
  ----------------------------------------------------------------

  WAVE-3. The two `ProjectedCertified` slots (qwen-coder-7b and
  llama-1b at k=8 PCA-only) had no pinned methodology. A default
  sovereign sieve would have REJECTED both and the wave-4
  falsification would never have been a surprise — it would have
  been the predicted outcome of attempting to ship an
  unmethologized projection.

  WAVE-15. The four mesh failures (KV cache OOM, trisplit panic,
  byte-fallback dominance, KV stride mismatch) are currently held
  in `Defer` status. The sovereign sieve QUEUES them for
  resolution rather than admitting them as deployment compromises.
  Each defer is a measurement-pending bule debt; the queue is the
  operational manifestation of the falsification ledger.

  ----------------------------------------------------------------
  PHANOPLANE / MONSTER MESH IMPLICATION
  ----------------------------------------------------------------

  The sovereign sieve is the gate in front of every node's
  deployment on the monster mesh. Each tri-g4 / cobordism-g4
  node's admission requires methodology pinning + bule
  expenditure. The 4 known mesh failures are not "shipped bugs";
  they're "Defer-status conjectures" awaiting resolution. The
  sieve is the discipline that prevents wave-3-style
  `ProjectedCertified` deployments from happening at the mesh
  layer.

  Init-only Lean 4. Zero sorries, zero axioms.
-/

import Gnosis.AntiTheory
import Gnosis.NoCloningTaxEqualsBuleCost
import Gnosis.ConjectureAsCommitment

namespace Gnosis
namespace SovereignSieveAsAntiTheoryGate

open Gnosis.AntiTheory
  (FalsifyingExperiment EmpiricalClaimStatus is_scientifically_meaningful
   current_status f1_cross_model_pca_at_K5
   f2_strict_K1_spec_decode_on_PCA f3_rank_density_invariant)

-- ══════════════════════════════════════════════════════════
-- 1. THE THREE-VALUED SIEVE DECISION
-- ══════════════════════════════════════════════════════════

/-- The sovereign sieve's verdict on a single `FalsifyingExperiment`.

    Three branches, three operational meanings:

    • `Admit` — the claim has cleared all three sieve checks
      (methodology pinned, bule budget met, zero counterexamples)
      and may cross the gate into production.

    • `Reject` — the claim fails at least one DISQUALIFYING check
      (methodology missing while required, or any counterexample
      present). Rejection is permanent for the current submission;
      the claim must be resubmitted as a new `FalsifyingExperiment`.

    • `Defer` — the claim is methodology-correct and counterexample-
      free but has not yet paid enough bule (witnesses) to clear
      the operational threshold. The sieve queues it pending
      further measurement. -/
inductive SieveDecision
  | Admit
  | Reject
  | Defer
  deriving DecidableEq, Repr

-- ══════════════════════════════════════════════════════════
-- 2. THE SOVEREIGN SIEVE STRUCTURE
-- ══════════════════════════════════════════════════════════

/-- The sovereign sieve, parameterized by its operational policy.

    Fields:

    * `operational_threshold_bule` — the minimum number of supporting
      measurement witnesses (bule units paid into the claim) before
      admission is permitted. Default `1`: admission requires at
      least one supporting measurement, never zero. Production-
      critical sieves can demand higher.

    * `methodology_required` — if `true` (anti-theory directive),
      a claim with `methodology_pinned = false` is REJECTED outright.
      If `false`, the methodology check is skipped (NOT recommended;
      documented for completeness).

    * `audit_log` — the sieve's own decision history. Every
      `apply_sieve` call SHOULD append a record (decision +
      hypothesis text); without the log the sieve is a black box
      and its decisions become unmeasurable. The list is the
      runtime mirror of the structural FalsificationLedger. -/
structure SovereignSieve where
  operational_threshold_bule : Nat
  methodology_required       : Bool
  audit_log                  : List String
  deriving Repr

-- ══════════════════════════════════════════════════════════
-- 3. THE SIEVE APPLICATION FUNCTION
-- ══════════════════════════════════════════════════════════

/-- Apply the sovereign sieve to a single `FalsifyingExperiment`.

    The decision proceeds in a fixed order — methodology check
    first (anti-theory rejection), counterexample check second
    (falsification rejection), bule-budget check third (defer
    if unpaid), admit otherwise:

      1. `!e.methodology_pinned && sieve.methodology_required`
         → `Reject`. The wave-3 `ProjectedCertified` pattern
           lands here.
      2. `e.counterexamples > 0` → `Reject`. The
         `FalsifiedByMeasurement` claims (F1, F2, F3, F4, F5)
         all land here.
      3. `e.witness_count < sieve.operational_threshold_bule`
         → `Defer`. Methodology correct, no counterexamples, but
         not enough bule paid yet — the claim queues for
         measurement.
      4. Otherwise → `Admit`. The healthy methodology-pinned,
         witness-supported, counterexample-free claim crosses
         the gate.

    The decision is total over the four cases; every
    `FalsifyingExperiment` produces exactly one
    `SieveDecision`. -/
def apply_sieve
    (sieve : SovereignSieve)
    (e : FalsifyingExperiment) : SieveDecision :=
  if !e.methodology_pinned && sieve.methodology_required then
    SieveDecision.Reject
  else if e.counterexamples > 0 then
    SieveDecision.Reject
  else if e.witness_count < sieve.operational_threshold_bule then
    SieveDecision.Defer
  else
    SieveDecision.Admit

-- ══════════════════════════════════════════════════════════
-- 4. NAMED SIEVE INSTANCES
-- ══════════════════════════════════════════════════════════

/-- The DEFAULT sovereign sieve. Threshold `1` (one supporting
    measurement minimum), methodology required (anti-theory
    directive enforced). This is the sieve that should sit in
    front of every production deployment by default. -/
def default_sovereign_sieve : SovereignSieve :=
  { operational_threshold_bule := 1
  , methodology_required       := true
  , audit_log                  := [] }

/-- The STRICT sovereign sieve. Threshold `3` (three supporting
    measurements minimum, mirroring the `ConjectureAsCommitment`
    promotion bar of three distinct methodologies), methodology
    required. Used in front of production-critical deployments
    where a single witness is insufficient. -/
def strict_sovereign_sieve : SovereignSieve :=
  { operational_threshold_bule := 3
  , methodology_required       := true
  , audit_log                  := [] }

/-- The PERMISSIVE sovereign sieve. Threshold `1` but methodology
    NOT required. Documented for completeness only — running this
    in production silently re-introduces the wave-3
    `ProjectedCertified` failure mode. NOT RECOMMENDED. -/
def permissive_sovereign_sieve : SovereignSieve :=
  { operational_threshold_bule := 1
  , methodology_required       := false
  , audit_log                  := [] }

-- ══════════════════════════════════════════════════════════
-- 5. WAVE-3 SUBMISSION RECORDS (the prevented mistakes)
-- ══════════════════════════════════════════════════════════

/-- The wave-3 qwen-coder-7b `ProjectedCertified` submission AS IT
    WAS — methodology NOT pinned (the projection was inherited from
    the qwen-0.5b sibling without an experiment design of its own).
    A default sovereign sieve REJECTS this; that rejection is
    exactly the protection the wave-3 ledger lacked. -/
def wave_3_qwen_coder_7b_projection : FalsifyingExperiment :=
  { hypothesis_text     :=
      "Qwen-Coder-7B at K=5 PCA-only is operationally certified (projected from 0.5B)"
  , methodology_pinned  := false
  , witness_count       := 0
  , counterexamples     := 0 }

/-- The wave-3 llama-1b `ProjectedCertified` submission AS IT WAS —
    same shape as the qwen-coder-7b one, same rejection by the
    default sovereign sieve. -/
def wave_3_llama_1b_projection : FalsifyingExperiment :=
  { hypothesis_text     :=
      "LLaMA-1B at k=8 PCA-only is operationally certified (projected from 0.5B)"
  , methodology_pinned  := false
  , witness_count       := 0
  , counterexamples     := 0 }

/-- The healthy qwen-0.5b measurement: methodology pinned, one
    supporting witness, zero counterexamples. This is the claim
    the wave-3 projections WANTED to look like; only this one
    actually does. -/
def qwen_0_5b_supported_measurement : FalsifyingExperiment :=
  { hypothesis_text     :=
      "Qwen2.5-0.5B at K=5 PCA-only certifies (F_eff = 1.00, 1 measurement)"
  , methodology_pinned  := true
  , witness_count       := 1
  , counterexamples     := 0 }

-- ══════════════════════════════════════════════════════════
-- 6. WAVE-3 GATING THEOREMS (decide-checked)
-- ══════════════════════════════════════════════════════════

/-- THE WAVE-3 PREVENTION THEOREM (qwen-coder-7b).

    The wave-3 `ProjectedCertified` claim for qwen-coder-7b had
    `methodology_pinned = false`. The default sovereign sieve
    rejects it on branch (1) of `apply_sieve`. This is the gate
    that would have prevented the wave-4 falsification. -/
theorem wave_3_qwen_coder_7b_projection_is_rejected_by_default_sieve :
    apply_sieve default_sovereign_sieve wave_3_qwen_coder_7b_projection
      = SieveDecision.Reject := by
  decide

/-- THE WAVE-3 PREVENTION THEOREM (llama-1b). Same gate, same
    rejection. -/
theorem wave_3_llama_1b_projection_is_rejected_by_default_sieve :
    apply_sieve default_sovereign_sieve wave_3_llama_1b_projection
      = SieveDecision.Reject := by
  decide

/-- THE HEALTHY-CLAIM ADMISSION THEOREM. The qwen-0.5b
    measurement clears all three sieve checks: methodology pinned,
    one witness ≥ threshold 1, zero counterexamples. Admitted. -/
theorem qwen_0_5b_supported_measurement_is_admitted_by_default_sieve :
    apply_sieve default_sovereign_sieve qwen_0_5b_supported_measurement
      = SieveDecision.Admit := by
  decide

-- ══════════════════════════════════════════════════════════
-- 7. THE F1-F5 UNIFORM REJECTION THEOREM
-- ══════════════════════════════════════════════════════════

/-- F4 ledger entry — the wave-8 honest-admission move on
    llama-1b, recast as a `FalsifyingExperiment` for sieve
    consumption. Methodology pinned (the audit IS the methodology),
    one counterexample (the projection itself, now refuted as
    vacuous). The sieve rejects on the counterexample branch. -/
def f4_llama_1b_projection_is_vacuous : FalsifyingExperiment :=
  { hypothesis_text     :=
      "LLaMA-1B k=8 PCA-only ProjectedCertified slot (refuted by audit)"
  , methodology_pinned  := true
  , witness_count       := 0
  , counterexamples     := 1 }

/-- F5 ledger entry — a sibling vacuous-projection admission on
    a parallel model. Same shape, same sieve verdict. -/
def f5_sibling_projection_is_vacuous : FalsifyingExperiment :=
  { hypothesis_text     :=
      "Sibling-model PCA-only ProjectedCertified slot (refuted by audit)"
  , methodology_pinned  := true
  , witness_count       := 0
  , counterexamples     := 1 }

/-- THE F1-F5 UNIFORM REJECTION THEOREM.

    All five permanent falsifications carry positive counterexample
    counts. The default sovereign sieve rejects each of them
    uniformly on branch (2) of `apply_sieve`. This is the
    runtime's first line of defense: refuted claims never reach
    production. -/
theorem all_five_falsified_experiments_are_rejected :
    apply_sieve default_sovereign_sieve f1_cross_model_pca_at_K5
      = SieveDecision.Reject
    ∧ apply_sieve default_sovereign_sieve f2_strict_K1_spec_decode_on_PCA
      = SieveDecision.Reject
    ∧ apply_sieve default_sovereign_sieve f3_rank_density_invariant
      = SieveDecision.Reject
    ∧ apply_sieve default_sovereign_sieve f4_llama_1b_projection_is_vacuous
      = SieveDecision.Reject
    ∧ apply_sieve default_sovereign_sieve f5_sibling_projection_is_vacuous
      = SieveDecision.Reject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

-- ══════════════════════════════════════════════════════════
-- 8. THE BULE-COST-FOR-ADMISSION THEOREM
-- ══════════════════════════════════════════════════════════

/-- THE NO-CLONING-TAX-FOR-ADMISSION THEOREM.

    For any `FalsifyingExperiment` admitted by the sieve, the
    witness count (= bule units paid into the claim's support
    ledger) is at least `sieve.operational_threshold_bule`.

    The sovereign sieve REFUSES to admit claims for free.
    Admission ALWAYS costs bule. This is the operational
    instantiation of `cannot_clone_measurement_without_bule_payment`
    from `Gnosis.NoCloningTaxEqualsBuleCost`: the structural
    no-cloning tax becomes the runtime's admission fee.

    The proof unfolds `apply_sieve` and works through the four
    branches. Only the final branch produces `Admit`, and the
    third-branch guard ensures `witness_count ≥ threshold` on
    that branch. -/
theorem sovereign_sieve_charges_bule_for_admission
    (sieve : SovereignSieve)
    (e : FalsifyingExperiment)
    (h : apply_sieve sieve e = SieveDecision.Admit) :
    e.witness_count ≥ sieve.operational_threshold_bule := by
  unfold apply_sieve at h
  by_cases h1 : !e.methodology_pinned && sieve.methodology_required
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : e.counterexamples > 0
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h
      by_cases h3 : e.witness_count < sieve.operational_threshold_bule
      · rw [if_pos h3] at h; cases h
      · exact Nat.le_of_not_lt h3

-- ══════════════════════════════════════════════════════════
-- 9. THE FOUR MESH FAILURES — DEFER STATUS
-- ══════════════════════════════════════════════════════════

/-- Mesh failure M1: gemma4-31b KV cache OOM under the 128 MiB
    Cloudflare Worker cap. Methodology pinned (the per-worker
    budget IS the falsification protocol — task #31 ships the
    kv_base_layer / kv_num_layers override), no counterexamples
    yet (the override has not been deployed and refuted). Witness
    count `0` < default threshold `1` → `Defer`. -/
def m1_kv_cache_oom : FalsifyingExperiment :=
  { hypothesis_text     :=
      "gemma4-31b kv_base_layer / kv_num_layers override fits the 128 MiB worker cap"
  , methodology_pinned  := true
  , witness_count       := 0
  , counterexamples     := 0 }

/-- Mesh failure M2: trisplit /split-a panics with "boot failed:
    unreachable" in wasm-only mode while native smoke is clean.
    Methodology pinned (debug build with console_panic_hook +
    bisect plan), no counterexamples. Defer pending the
    bisect. -/
def m2_trisplit_panic : FalsifyingExperiment :=
  { hypothesis_text     :=
      "trisplit /split-a wasm panic isolates to a single bisectable revision"
  , methodology_pinned  := true
  , witness_count       := 0
  , counterexamples     := 0 }

/-- Mesh failure M3: byte-fallback dominance in the Rust
    gemma4 kernel (mirrors the pre-v196 Aether symptom).
    Methodology pinned, no counterexamples. Defer pending the
    fix list inline. -/
def m3_byte_fallback_dominance : FalsifyingExperiment :=
  { hypothesis_text     :=
      "byte-fallback dominance in gemma4 kernel resolves under the documented fix list"
  , methodology_pinned  := true
  , witness_count       := 0
  , counterexamples     := 0 }

/-- Mesh failure M4: KV cache stride mismatch (known but
    separate from M1). Methodology pinned, no counterexamples.
    Defer pending the parallel investigation. -/
def m4_kv_stride_mismatch : FalsifyingExperiment :=
  { hypothesis_text     :=
      "KV cache stride mismatch in gemma4 mesh resolves under the parallel investigation"
  , methodology_pinned  := true
  , witness_count       := 0
  , counterexamples     := 0 }

/-- THE MESH-FAILURES-ARE-AT-THE-SIEVE THEOREM.

    All four currently-open mesh failures (KV OOM, trisplit panic,
    byte-fallback dominance, KV stride) are methodology-pinned and
    counterexample-free but witness-count `0` — short of the
    default threshold `1`. The sovereign sieve places each of
    them in `Defer` status: queued for measurement, NOT shipped
    as deployment compromises. -/
theorem mesh_failures_are_currently_at_the_sieve :
    apply_sieve default_sovereign_sieve m1_kv_cache_oom
      = SieveDecision.Defer
    ∧ apply_sieve default_sovereign_sieve m2_trisplit_panic
      = SieveDecision.Defer
    ∧ apply_sieve default_sovereign_sieve m3_byte_fallback_dominance
      = SieveDecision.Defer
    ∧ apply_sieve default_sovereign_sieve m4_kv_stride_mismatch
      = SieveDecision.Defer := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals decide

-- ══════════════════════════════════════════════════════════
-- 10. THE ANTI-THEORY-ENFORCEMENT THEOREM
-- ══════════════════════════════════════════════════════════

/-- THE ANTI-THEORY-ENFORCEMENT THEOREM.

    For any `FalsifyingExperiment` that is NOT scientifically
    meaningful per `Gnosis.AntiTheory.is_scientifically_meaningful`
    (i.e. methodology not pinned OR no measurements taken at all),
    the default sovereign sieve returns either `Reject` or
    `Defer` — NEVER `Admit`.

    Vacuous claims, by construction, never pass the gate. The
    sovereign sieve is the runtime instantiation of anti-theory's
    central directive: "an unmethologized claim is vacuous from
    the start, not true until refuted." -/
theorem sovereign_sieve_enforces_anti_theory_directive
    (e : FalsifyingExperiment)
    (h : is_scientifically_meaningful e = false) :
    apply_sieve default_sovereign_sieve e ≠ SieveDecision.Admit := by
  unfold is_scientifically_meaningful at h
  unfold apply_sieve
  -- `default_sovereign_sieve.methodology_required = true`,
  -- `default_sovereign_sieve.operational_threshold_bule = 1`.
  -- Case-split on `e.methodology_pinned`.
  by_cases hM : e.methodology_pinned = true
  · -- methodology pinned: conjunct (a) is true, so for the AND
    -- in `is_scientifically_meaningful` to be false, conjunct (b)
    -- must be false: no measurements taken.
    rw [hM] at h
    simp at h
    -- After `simp`, `h` is `e.witness_count + e.counterexamples = 0`
    -- (or, in some versions, a conjunction). Robustly extract both.
    have hW : e.witness_count = 0 := by omega
    have hC : e.counterexamples = 0 := by omega
    -- Walk the four branches of apply_sieve.
    rw [hM, hC, hW]
    decide
  · -- methodology NOT pinned → first branch fires → Reject
    have hMF : e.methodology_pinned = false := by
      cases hp : e.methodology_pinned with
      | false => rfl
      | true  => exact absurd hp hM
    rw [hMF]
    simp
    intro hAbs
    cases hAbs

-- ══════════════════════════════════════════════════════════
-- 11. THE COMMITMENT-BRIDGE THEOREM
-- ══════════════════════════════════════════════════════════

/-- A bridge between `Gnosis.ConjectureAsCommitment.Conjecture`
    and `FalsifyingExperiment` for sieve consumption.

    A committed conjecture maps to a methodology-pinned
    `FalsifyingExperiment` whose witness count starts at `0` and
    grows as measurements arrive. An uncommitted conjecture maps
    to a methodology-UNPINNED experiment, since "no owner" is the
    runtime equivalent of "no methodology". -/
def conjecture_to_experiment
    (c : Gnosis.ConjectureAsCommitment.Conjecture)
    (witnesses : Nat)
    (counters  : Nat) : FalsifyingExperiment :=
  { hypothesis_text     := c.claim_text
  , methodology_pinned  := c.is_committed
  , witness_count       := witnesses
  , counterexamples     := counters }

/-- THE COMMITTED-CONJECTURE-PROGRESSION THEOREM.

    A committed conjecture (in the sense of
    `Gnosis.ConjectureAsCommitment`) starts in `Defer` status with
    zero witnesses, transitions to `Admit` once it accumulates
    enough supporting measurements to clear the bule threshold,
    and transitions to `Reject` if a counterexample arrives. The
    sieve is the runtime's queue manager for committed
    conjectures.

    Proved for the C1 conjecture as the canonical witness; the
    same shape holds for any committed conjecture by construction
    of `conjecture_to_experiment`. -/
theorem committed_conjectures_pass_sieve_when_witness_arrives :
    -- (a) zero witnesses, zero counterexamples → Defer
    apply_sieve default_sovereign_sieve
      (conjecture_to_experiment
        Gnosis.ConjectureAsCommitment.c1_K_widening_rescues_at_scale 0 0)
      = SieveDecision.Defer
    -- (b) one witness arrives → Admit
    ∧ apply_sieve default_sovereign_sieve
        (conjecture_to_experiment
          Gnosis.ConjectureAsCommitment.c1_K_widening_rescues_at_scale 1 0)
        = SieveDecision.Admit
    -- (c) a counterexample arrives → Reject (even with witnesses)
    ∧ apply_sieve default_sovereign_sieve
        (conjecture_to_experiment
          Gnosis.ConjectureAsCommitment.c1_K_widening_rescues_at_scale 5 1)
        = SieveDecision.Reject := by
  refine ⟨?_, ?_, ?_⟩
  all_goals decide

-- ══════════════════════════════════════════════════════════
-- 12. THE MONSTER-MESH-PROTECTION THEOREM
-- ══════════════════════════════════════════════════════════

/-- The list of currently-open mesh failures. Used by the
    monster-mesh protection theorem below. -/
def open_mesh_failures : List FalsifyingExperiment :=
  [ m1_kv_cache_oom
  , m2_trisplit_panic
  , m3_byte_fallback_dominance
  , m4_kv_stride_mismatch ]

/-- THE MONSTER-MESH-PROTECTED-BY-SOVEREIGN-SIEVE THEOREM.

    Every entry on the open mesh failure list lands in `Defer`
    under the default sovereign sieve. None are admitted; none
    are rejected. The sieve holds them in queue, which means
    each is a Defer-status conjecture awaiting measurement
    rather than a shipped deployment compromise.

    The phanoplane / monster mesh discipline is exactly this:
    no node ships its known failures; each known failure sits at
    the gate, waiting for the bule expenditure (the measurement
    work) that resolves it. -/
theorem monster_mesh_protected_by_sovereign_sieve :
    open_mesh_failures.all
      (fun e => decide (apply_sieve default_sovereign_sieve e
                        = SieveDecision.Defer))
      = true := by
  decide

-- ══════════════════════════════════════════════════════════
-- 13. THE AUDIT-LOG ACCOUNTABILITY THEOREM
-- ══════════════════════════════════════════════════════════

/-- Append a sieve decision to the audit log. The log entry is
    a single string combining the decision tag and the
    hypothesis text — enough for an operator to reconstruct
    the gate's recent history without consulting external
    state. -/
def log_decision
    (sieve : SovereignSieve)
    (e : FalsifyingExperiment)
    (d : SieveDecision) : SovereignSieve :=
  let tag := match d with
    | SieveDecision.Admit  => "ADMIT  : "
    | SieveDecision.Reject => "REJECT : "
    | SieveDecision.Defer  => "DEFER  : "
  { sieve with audit_log := sieve.audit_log ++ [tag ++ e.hypothesis_text] }

/-- A single sieve-and-log step: apply the sieve and append the
    decision to the audit log. Returns the updated sieve and the
    decision. -/
def sieve_and_log
    (sieve : SovereignSieve)
    (e : FalsifyingExperiment) : SovereignSieve × SieveDecision :=
  let d := apply_sieve sieve e
  (log_decision sieve e d, d)

/-- THE AUDIT-LOG-ACCOUNTABILITY THEOREM.

    Every `sieve_and_log` step extends the audit log by exactly
    one entry. Operationally, this means: the sieve cannot
    silently process a `FalsifyingExperiment` — every decision
    leaves a trace. Without the trace, the sieve's verdicts
    become unmeasurable, which is itself a violation of the
    anti-theory directive (a black-box gate is an unmethologized
    decision procedure). -/
theorem sieve_decisions_must_be_logged_for_accountability
    (sieve : SovereignSieve)
    (e : FalsifyingExperiment) :
    (sieve_and_log sieve e).fst.audit_log.length
      = sieve.audit_log.length + 1 := by
  unfold sieve_and_log log_decision
  cases apply_sieve sieve e <;> simp

-- ══════════════════════════════════════════════════════════
-- 14. THE STRICT-SIEVE DEFER THEOREM
-- ══════════════════════════════════════════════════════════

/-- THE STRICT-SIEVE-DEFERS-SINGLE-WITNESS THEOREM.

    The qwen-0.5b measurement (one witness) is admitted by the
    DEFAULT sieve but DEFERRED by the STRICT sieve, which
    requires three witnesses. This is the production-critical
    discipline: a single supporting measurement is enough for
    development admission but not enough for production-critical
    promotion. -/
theorem strict_sieve_defers_single_witness :
    apply_sieve strict_sovereign_sieve qwen_0_5b_supported_measurement
      = SieveDecision.Defer := by
  decide

/-- THE PERMISSIVE-SIEVE-IS-A-WAVE-3-FOOTGUN THEOREM.

    The wave-3 qwen-coder-7b projection — methodology unpinned —
    is REJECTED by the default sieve but DEFERRED by the
    permissive sieve. The permissive sieve fails to enforce the
    anti-theory directive; it only blocks on counterexamples and
    bule, not on methodology. This is documented as a footgun:
    the permissive sieve silently re-introduces the wave-3
    failure mode. -/
theorem permissive_sieve_fails_to_reject_wave_3_projection :
    apply_sieve permissive_sovereign_sieve wave_3_qwen_coder_7b_projection
      = SieveDecision.Defer := by
  decide

end SovereignSieveAsAntiTheoryGate
end Gnosis
