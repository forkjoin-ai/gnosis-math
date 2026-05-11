/-
  AmplituhedronCoordinatorContract.lean
  =====================================

  Pins the host-side coordinator's behavioral invariants as theorems.
  Mirrors `AmplituhedronFalsifiability`'s runtime-oracle pentad and the
  contract style of `AckermannAdmissionContract`.

  ## Context

  The 2026-05-10 landing of the host-side Amplituhedron coordinator loop
  at `apps/distributed-inference-host/src/pipeline.ts` introduced a
  four-step replay flow (per `open-source/gnosis/distributed-inference/
  AMPLITUHEDRON_PLAN.md §4`):

    1. `prefix_hash = hash(promptTokens)` — deterministic on the prompt.
    2. Fan-out replay query to every station — Boolean conjunction over
       per-station hit/miss verdicts.
    3. All-hit branch: skip prefill, decode straight from the cached tail
       residual.
    4. Any-miss branch: run pipelined prefill, capture per station
       (fire-and-forget) for the next request.

  This module pins the structural invariants the host TS code MUST
  reproduce on canonical witnesses. The numeric `14336` used in the
  hit-arity witnesses is the symbolic tail-residual byte length
  `hidden_dim × sizeof(f32) = 3584 × 4` for qwen-coder-7b; any positive
  `Nat` would discharge the proofs identically.

  Imports `Init` plus the upstream amplituhedron modules. Zero `sorry`,
  zero new `axiom`. Init-only Lean.
-/

import Init
import Gnosis.AmplituhedronAttention
import Gnosis.AmplituhedronFalsifiability

namespace AmplituhedronCoordinatorContract

open AmplituhedronAttention
open AmplituhedronFalsifiability

/-! ## Per-station replay verdict

A station either hits (returns the tail residual byte slab) or misses
(no entry for the current `(prefix_hash, prefix_len, layer_lo,
layer_hi)` key). The coordinator combines verdicts across N stations
via Boolean conjunction. -/

/-- A replay verdict from a single station: either a hit carrying the
    tail residual byte length, or a miss. -/
inductive ReplayVerdict where
  | hit (tailResidualLen : Nat)    -- tail residual bytes available
  | miss                           -- station has no entry for this key
  deriving DecidableEq, Repr

/-- Coordinator decision: "skip prefill" iff every station hit.

    The host code must additionally guard on `verdicts.nonEmpty` before
    skipping prefill — `List.all` is vacuously `true` on the empty list,
    but a zero-station coordinator has no cached tail to seed from. -/
def coordinatorDecision (verdicts : List ReplayVerdict) : Bool :=
  verdicts.all (fun v => match v with | .hit _ => true | .miss => false)

/-! ## Behavioral contracts

Each theorem here pins one decision the host coordinator must take on
a canonical witness. The host's unit tests in
`apps/distributed-inference-host/src/pipeline.test.ts` (or equivalent
surface) must exhibit the same verdict on the same witness shape. -/

/-- The vacuous-on-empty decision value. Named so the host code's
    `verdicts.length === 0` guard is legible against this constant: if
    the host ever sees an empty verdict list, it must NOT treat
    `coordinatorDecisionOnEmpty = true` as license to skip prefill. -/
def coordinatorDecisionOnEmpty : Bool := coordinatorDecision []

/-- **Contract #1 (empty-list vacuity).** The Boolean decision on zero
    stations evaluates to `true` by `List.all` on the empty list. The
    host MUST additionally require a non-empty station list before
    skipping prefill; this theorem exists so the host's guard predicate
    has a Lean-side anchor. -/
theorem coordinator_empty_is_vacuously_true :
    coordinatorDecisionOnEmpty = true := by
  unfold coordinatorDecisionOnEmpty coordinatorDecision
  decide

/-- **Contract #2 (single hit ⇒ skip).** A single hit station decides
    to skip prefill. The host's all-hit branch fires here. -/
theorem coordinator_single_hit_skips :
    coordinatorDecision [ReplayVerdict.hit 14336] = true := by
  unfold coordinatorDecision; decide

/-- **Contract #3 (single miss ⇒ no skip).** A single miss station
    decides not to skip prefill. The host's any-miss branch fires. -/
theorem coordinator_single_miss_does_not_skip :
    coordinatorDecision [ReplayVerdict.miss] = false := by
  unfold coordinatorDecision; decide

/-- **Contract #4 (any miss in N ⇒ no skip).** With at least one miss
    in a multi-station fan-out, the coordinator must not skip prefill.
    Mirror witness: `[hit, miss, hit]`. -/
theorem coordinator_any_miss_does_not_skip :
    coordinatorDecision
      [ReplayVerdict.hit 14336, ReplayVerdict.miss, ReplayVerdict.hit 14336]
      = false := by
  unfold coordinatorDecision; decide

/-- **Contract #5 (all hit in N ⇒ skip).** With all stations hitting,
    the coordinator must skip prefill and seed decode from the cached
    tail. Mirror witness: three-station all-hit. -/
theorem coordinator_all_hit_skips :
    coordinatorDecision
      [ReplayVerdict.hit 14336, ReplayVerdict.hit 14336, ReplayVerdict.hit 14336]
      = true := by
  unfold coordinatorDecision; decide

/-! ## Composition with Death #1 (MatVecMemo) per AMPLITUHEDRON_PLAN §5

When the coordinator decides to skip prefill, decode must enter via the
cached-replay path, not the fresh-prefill path. Death #1 (matVec memo,
intra-layer) and Death #2 (amplituhedron volume cache, inter-layer)
compose orthogonally on disjoint key spaces, as already noted in
`AmplituhedronFalsifiability.death1_death2_keys_disjoint`.

There is no MatVecMemo formalization to import here, so the composition
rule is encoded as a structural predicate on the post-replay decode
entry: the decode-entry mode must agree with the coordinator decision. -/

/-- The decode-entry mode the host records immediately after the
    coordinator decision. -/
inductive DecodeEntry where
  | viaCachedReplay   -- coordinator hit; seed from cached tail
  | viaFreshPrefill   -- coordinator miss; ran pipelinedPrefill
  deriving DecidableEq, Repr

/-- Map a coordinator decision to the corresponding decode-entry mode.
    The host's pipeline branch selector must agree with this map. -/
def decodeEntryFromDecision (decision : Bool) : DecodeEntry :=
  if decision then DecodeEntry.viaCachedReplay
  else DecodeEntry.viaFreshPrefill

/-- **Composition correctness.** `decodeEntryFromDecision` agrees with
    the coordinator branch on both possible decisions. The host code
    MUST select `viaCachedReplay` on `true` and `viaFreshPrefill` on
    `false`; any other mapping is wrong. -/
theorem decode_entry_from_decision_correctness :
    decodeEntryFromDecision true = DecodeEntry.viaCachedReplay ∧
    decodeEntryFromDecision false = DecodeEntry.viaFreshPrefill := by
  unfold decodeEntryFromDecision; refine ⟨?_, ?_⟩ <;> decide

/-! ## Bundled pentad

Single statement carrying the five coordinator contracts plus the
decode-entry composition. The host's pipeline test surface mirrors this
point-for-point; any deviation in the host TS code falsifies one of
these conjuncts. -/

/-- **Bundled coordinator-contract pentad.** Five behavioral
    invariants the host coordinator MUST exhibit, packaged as a single
    `And`-chain so the host test surface can mirror them in one shot.
    Conjuncts in order:

    1. single-hit decision is `true` (skip prefill),
    2. single-miss decision is `false` (run prefill),
    3. any-miss in three-station fan-out is `false` (run prefill),
    4. all-hit in three-station fan-out is `true` (skip prefill),
    5. `decodeEntryFromDecision true = viaCachedReplay` (composition
       with Death #1: the skip-prefill branch enters decode via the
       cached-replay path). -/
theorem amplituhedron_coordinator_contract_pentad :
    coordinatorDecision [ReplayVerdict.hit 14336] = true ∧
    coordinatorDecision [ReplayVerdict.miss] = false ∧
    coordinatorDecision
      [ReplayVerdict.hit 14336, ReplayVerdict.miss, ReplayVerdict.hit 14336]
      = false ∧
    coordinatorDecision
      [ReplayVerdict.hit 14336, ReplayVerdict.hit 14336, ReplayVerdict.hit 14336]
      = true ∧
    decodeEntryFromDecision true = DecodeEntry.viaCachedReplay :=
  ⟨coordinator_single_hit_skips,
   coordinator_single_miss_does_not_skip,
   coordinator_any_miss_does_not_skip,
   coordinator_all_hit_skips,
   decode_entry_from_decision_correctness.1⟩

end AmplituhedronCoordinatorContract
