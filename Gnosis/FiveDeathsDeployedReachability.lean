import Init

/-
  FiveDeathsDeployedReachability.lean
  ===================================

  Deploy-side reachability companion to
  `Gnosis.FiveDeathsCompositionOrthogonality`.

  ## Why this file exists

  As of 2026-05-10 (S4 empirical sweep), the deployed
  `distributed-inference-worker-production.taylorbuley.workers.dev`
  exposes two HTTP entry points that touch the Five Deaths cache stack:

  * `/forward`     — single-call full prefill, dispatches
                     `forward_range_chunk` which calls **raw**
                     `mat_vec_f32` (Death #1's `cached_mat_vec`
                     never fires).
  * `/forward-one` — split-phase exports (`forward_one`,
                     `attention_only`, `ffn_only`) DO call
                     `cached_mat_vec`, and `wasm_bindings.rs:529`
                     captures the amplituhedron volume.

  The composition orthogonality theorem in
  `FiveDeathsCompositionOrthogonality` proves that Death #1's
  `MatVecKey` and Death #2's `AmplituhedronKey` cannot collide
  at the type level. That theorem is structurally true regardless
  of which handler is wired — but it is **operationally meaningful**
  only when both caches actually fire on the same prefill. When one
  side never fires, the theorem holds vacuously: there is nothing
  to compose with.

  This file makes that dichotomy precise. It introduces a
  `HandlerInvocation` record describing which cache-instrumented
  kernels a deployed handler reaches, and proves that the
  `/forward` handler as deployed today exhibits the **vacuous**
  case while `/forward-one` exhibits the **nontrivial** case.

  ## What's formalized

  * `HandlerInvocation` — a record naming a deployed handler and
    the two cache-bool flags `invokes_matvec_memo` (Death #1) and
    `invokes_amplituhedron` (Death #2).
  * `OrthogonalityVacuous` — the predicate "at least one of the
    two caches is never reached on this handler's prefill path".
  * `OrthogonalityNontrivial` — the predicate "both caches are
    reached on this handler's prefill path".
  * `composition_holds_nontrivially_iff_both_invoked` — the
    structural theorem from `FiveDeathsCompositionOrthogonality`
    is exercised on the production hot path iff
    `OrthogonalityNontrivial h`. If `OrthogonalityVacuous h`
    then the composition theorem holds trivially (one operand
    is identically the empty cache), and the deployed runtime
    is not yet a witness to the structural property.
  * `forward_handler_2026_05_10` — concrete witness of `/forward`
    as deployed today: `invokes_matvec_memo = false`,
    `invokes_amplituhedron = true`.
  * `forward_one_handler_2026_05_10` — concrete witness of
    `/forward-one` as deployed today: both `true`.
  * `forward_handler_orthogonality_is_vacuous` — `decide`-proved
    instance of the vacuous case on the production `/forward` path.
  * `forward_one_handler_orthogonality_is_nontrivial` —
    `decide`-proved instance of the nontrivial case on the
    production `/forward-one` path.
  * `deploy_recommendation` — informative theorem documenting
    the production-deploy gap measured by S4: switch the
    coordinator's prefill dispatch from `/forward` to
    `/forward-one` (or extend `forward_range_chunk` to call
    `cached_mat_vec`) so that the structural orthogonality
    theorem is operationally exercised.

  ## Operational caveat (cite S1)

  Reachability of both caches is necessary but not sufficient
  for the structural theorem to be operationally exercised.
  S1 (2026-05-10 empirical sweep) found that even on
  `/forward-one`, where Death #2 IS wired, the per-phase
  amplituhedron key was non-deterministic across warm calls,
  so cache hits stayed at zero. The full operational predicate
  is therefore a conjunction:

    operationally_orthogonal h  :=
      OrthogonalityNontrivial h
      ∧ cache_keys_deterministic_across_warm_calls h

  This file formalizes only the first conjunct (reachability).
  The second conjunct (key determinism) is a separate runtime
  invariant tracked outside this Lean module.

  ## Scope of the Lean claim

  This file does **not** prove that the deployed handler MUST
  invoke both caches. That is a runtime assertion about Rust /
  TypeScript code, not a Lean theorem. The Lean side just makes
  the dichotomy precise so the deploy gap is formally legible:
  which handler witnesses the composition theorem, and which
  does not.

  Init-only per the Rustic Church initiative.
-/

namespace FiveDeathsDeployedReachability

-- ══════════════════════════════════════════════════════════
-- HANDLER INVOCATION RECORD
-- ══════════════════════════════════════════════════════════

/-- A record of which cache-instrumented kernels a deployed HTTP
    handler invokes per prefill.

    * `handler_name` — the URL path (e.g. `"/forward"`,
      `"/forward-one"`).
    * `invokes_matvec_memo` — true iff this handler's prefill
      path reaches Death #1's `cached_mat_vec` (vs raw
      `mat_vec_f32`).
    * `invokes_amplituhedron` — true iff this handler's prefill
      path reaches Death #2's `amplituhedron::capture`. -/
structure HandlerInvocation where
  handler_name : String
  invokes_matvec_memo : Bool
  invokes_amplituhedron : Bool
  deriving Repr, DecidableEq

-- ══════════════════════════════════════════════════════════
-- VACUOUS vs NONTRIVIAL ORTHOGONALITY
-- ══════════════════════════════════════════════════════════

/-- An invocation is **vacuous** for orthogonality purposes if at
    least one of the two cache-instrumented kernels is never
    reached. The composition theorem still holds — there is no
    collision because one operand is the empty cache — but the
    deployed runtime is not a witness to the structural property. -/
@[reducible] def OrthogonalityVacuous (h : HandlerInvocation) : Prop :=
  ¬(h.invokes_matvec_memo = true ∧ h.invokes_amplituhedron = true)

/-- An invocation is **nontrivial** for orthogonality purposes if
    both cache-instrumented kernels are reached on the same
    prefill. This is the regime in which the composition
    orthogonality theorem from `FiveDeathsCompositionOrthogonality`
    is operationally exercised. -/
@[reducible] def OrthogonalityNontrivial (h : HandlerInvocation) : Prop :=
  h.invokes_matvec_memo = true ∧ h.invokes_amplituhedron = true

/-- The two predicates partition the handler space: every handler
    is either vacuous or nontrivial, never both. -/
theorem vacuous_or_nontrivial (h : HandlerInvocation) :
    OrthogonalityVacuous h ∨ OrthogonalityNontrivial h := by
  by_cases hb : h.invokes_matvec_memo = true ∧ h.invokes_amplituhedron = true
  · exact Or.inr hb
  · exact Or.inl hb

/-- Decidable `Bool`-level mirror of `OrthogonalityNontrivial`,
    suitable for `decide` proofs on concrete witnesses. -/
def isOrthogonalityNontrivial (h : HandlerInvocation) : Bool :=
  h.invokes_matvec_memo && h.invokes_amplituhedron

/-- Decidable `Bool`-level mirror of `OrthogonalityVacuous`. -/
def isOrthogonalityVacuous (h : HandlerInvocation) : Bool :=
  !(h.invokes_matvec_memo && h.invokes_amplituhedron)

-- ══════════════════════════════════════════════════════════
-- COMPOSITION-NONTRIVIALITY EQUIVALENCE
-- ══════════════════════════════════════════════════════════

/-- **`Gnosis.FiveDeathsCompositionOrthogonality.stack_composition_independent`
    is operationally meaningful on a deployed handler iff that
    handler is `OrthogonalityNontrivial`.**

    The structural theorem holds for every handler — it is a
    type-level claim about `MatVecKey` vs `AmplituhedronKey`.
    But it is exercised on the production hot path only when both
    caches actually fire. The forward direction says: if both fire,
    the composition is nontrivially exercised. The reverse says:
    if the composition is nontrivially exercised, both fire.

    This is a tautology by design — the predicate
    `OrthogonalityNontrivial` IS the operational meaning of
    "both caches participated in this prefill". The theorem
    just records that equivalence so downstream Lean code can
    cite it. -/
theorem composition_holds_nontrivially_iff_both_invoked
    (h : HandlerInvocation) :
    OrthogonalityNontrivial h ↔
      (h.invokes_matvec_memo = true ∧ h.invokes_amplituhedron = true) :=
  Iff.rfl

/-- Symmetric: the vacuous regime is exactly the negation. -/
theorem vacuous_iff_some_cache_missing (h : HandlerInvocation) :
    OrthogonalityVacuous h ↔
      ¬(h.invokes_matvec_memo = true ∧ h.invokes_amplituhedron = true) :=
  Iff.rfl

-- ══════════════════════════════════════════════════════════
-- DEPLOYED HANDLER WITNESSES (2026-05-10)
-- ══════════════════════════════════════════════════════════

/-- The `/forward` handler as deployed on
    `distributed-inference-worker-production.taylorbuley.workers.dev`
    on 2026-05-10. Per S4's empirical sweep:

    * `invokes_matvec_memo = false` — `forward_range_chunk`
      dispatches raw `mat_vec_f32`; Death #1's `cached_mat_vec`
      is never reached.
    * `invokes_amplituhedron = true` — `wasm_bindings.rs:529`
      captures the amplituhedron volume on every prefill. -/
def forward_handler_2026_05_10 : HandlerInvocation :=
  { handler_name := "/forward"
    invokes_matvec_memo := false
    invokes_amplituhedron := true }

/-- The `/forward-one` handler as deployed on the same Worker on
    2026-05-10. The split-phase exports `forward_one`,
    `attention_only`, and `ffn_only` DO call `cached_mat_vec`,
    and the same `wasm_bindings.rs:529` amplituhedron capture
    fires. -/
def forward_one_handler_2026_05_10 : HandlerInvocation :=
  { handler_name := "/forward-one"
    invokes_matvec_memo := true
    invokes_amplituhedron := true }

-- ══════════════════════════════════════════════════════════
-- DECIDABLE WITNESSES
-- ══════════════════════════════════════════════════════════

/-- **The `/forward` handler's orthogonality is vacuous as
    deployed today.** Death #1 never fires on its prefill path,
    so the composition orthogonality theorem holds trivially —
    the deployed runtime is not a witness to the structural
    property on this endpoint. Proved by `decide`. -/
theorem forward_handler_orthogonality_is_vacuous :
    OrthogonalityVacuous forward_handler_2026_05_10 := by
  decide

/-- **The `/forward-one` handler's orthogonality is nontrivial
    as deployed today.** Both Death #1 and Death #2 fire on its
    prefill path, so the composition orthogonality theorem from
    `FiveDeathsCompositionOrthogonality` is operationally
    exercised. Proved by `decide`. -/
theorem forward_one_handler_orthogonality_is_nontrivial :
    OrthogonalityNontrivial forward_one_handler_2026_05_10 := by
  decide

-- ══════════════════════════════════════════════════════════
-- DEPLOY RECOMMENDATION (INFORMATIVE)
-- ══════════════════════════════════════════════════════════

/-- **Production-deploy gap recorded by S4 on 2026-05-10.**

    The coordinator's prefill dispatch currently routes through
    `/forward` (vacuous) instead of `/forward-one` (nontrivial).
    The composition orthogonality theorem from
    `FiveDeathsCompositionOrthogonality` is therefore not
    operationally exercised on the production hot path.

    Two equivalent fixes close the gap:

    1. Switch the coordinator dispatch from `/forward` to
       `/forward-one` so Death #1's `cached_mat_vec` fires.
    2. Extend `forward_range_chunk` to call `cached_mat_vec`
       directly, lifting `/forward` from vacuous to nontrivial.

    This theorem is informative — it documents the gap as a
    pair of `decide`-proved facts. It is NOT a proof obligation
    on the deployment; runtime claims about Rust dispatch
    cannot be proved in Lean. -/
theorem deploy_recommendation :
    OrthogonalityNontrivial forward_one_handler_2026_05_10
    ∧ OrthogonalityVacuous forward_handler_2026_05_10 :=
  ⟨forward_one_handler_orthogonality_is_nontrivial,
   forward_handler_orthogonality_is_vacuous⟩

-- ══════════════════════════════════════════════════════════
-- S1 OPERATIONAL CAVEAT (cache key determinism)
-- ══════════════════════════════════════════════════════════

/-
  S1's 2026-05-10 sweep found that even on `/forward-one`, where
  Death #2 IS wired into the prefill path, the per-phase
  amplituhedron key was non-deterministic across warm calls —
  the captured `prefix_hash` shifted between identical-input
  invocations, so the LRU cache reported zero hits in steady
  state.

  Operational orthogonality therefore requires BOTH:

    (a) Both caches reachable on the prefill path
        (formalized above as `OrthogonalityNontrivial`).
    (b) Cache keys deterministic across warm calls with
        identical inputs (a separate runtime invariant,
        not formalized in this Lean module).

  Conjunct (a) is necessary but not sufficient. A handler that
  passes `OrthogonalityNontrivial` can still produce a zero
  cache-hit rate if conjunct (b) fails. Tracking (b) belongs in
  runtime instrumentation (cache-stats counters, key-hash
  determinism asserts), not in this file.
-/

end FiveDeathsDeployedReachability
