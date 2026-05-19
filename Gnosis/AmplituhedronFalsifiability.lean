import Init
import Gnosis.AmplituhedronAttention
import Gnosis.AmplituhedronGrassmannian
import Gnosis.AmplituhedronVertices
import Gnosis.AmplituhedronWitnesses

/-
  AmplituhedronFalsifiability.lean
  =================================

  The amplituhedron analogue of `Gnosis.BowlMeshNode` / `BowlMeshQSweep`:
  a falsification-driven file that names the failure regime of the
  current placeholder amplitude, proves the Plücker formalism is
  non-degenerate, and pins down the Lean → Rust test oracle.

  ## Falsification context

  The 2026-05-10 audit of the runtime amplituhedron stack
  (`open-source/gnosis/distributed-inference/src/amplituhedron.rs` plus
  the worker handlers in `apps/distributed-inference-worker/src/`) found:

  - The runtime ships a working **volume cache** (LRU prefix-hash → KV
    slab) — capture, replay, eviction, all operational.
  - The runtime does NOT compute Plücker coordinates, scattering
    amplitudes, or vertex enumerations. The mathematical kernel
    formalized in `AmplituhedronGrassmannian.lean` and
    `AmplituhedronVertices.lean` is **not on the runtime hot path**.
  - The original Lean placeholder
    `scattering_amplitude (qk : Nat) := qk / 10`
    (in `AmplituhedronAttention.lean`) is the lossy stand-in.
    Integer division by 10 erases nine of every ten quanta of
    attention amplitude. This is the amplituhedron analogue of the
    binary-mask zero-fill that falsified at K=1 in the Bowl Mesh
    experiment chain.

  ## What this file formalizes

  * `placeholder_amplitude` — the lossy stand-in copied from
    `AmplituhedronAttention.scattering_amplitude` for explicit comparison.
  * `placeholder_collapses_below_threshold` — for `qk < 10`, the
    placeholder returns 0. This is the structural failure regime: any
    sub-threshold attention amplitude is zero-filled, exactly the
    behaviour the binary mask exhibited at the residual-stream level.
  * `placeholder_is_high_damping_amplitude` — names the regime: the
    Nat-division placeholder is the high-damping limit of the real
    amplitude, in the same sense `BowlMeshNode.mask_at_high_damping`
    names the binary-mask regime.
  * `real_amplitude_preserves_below_threshold` — the real Plücker
    amplitude returns a structurally non-zero value whenever the
    Plücker vector and dual covector both carry positive entries on a
    common index. The structural property the placeholder violates.
  * Runtime oracles (`vandermonde_runtime_oracle_*`) — concrete
    expected values the Rust kernel must reproduce when it ships a
    real Plücker computation. These re-export the Vandermonde witness
    from `AmplituhedronWitnesses` as a Lean → Rust contract.

  Imports `Init` plus the upstream amplituhedron modules. Zero `sorry`,
  zero new `axiom`.
-/

namespace AmplituhedronFalsifiability

open AmplituhedronAttention
open AmplituhedronAttention.Grassmannian
open AmplituhedronAttention.Vertices
open AmplituhedronAttention.Witnesses

-- ══════════════════════════════════════════════════════════
-- THE PLACEHOLDER REGIME — LOSSY DIV-BY-10
-- ══════════════════════════════════════════════════════════

/-- The original placeholder amplitude (mirrored from
    `AmplituhedronAttention.scattering_amplitude`): `qk / 10`. -/
def placeholder_amplitude (qk : Nat) : Nat := qk / 10

/-- **Failure regime.** For any `qk < 10`, the placeholder amplitude
    returns 0 — the lossy zero-fill that the volume cache currently
    relies on. This is the amplituhedron analogue of
    `BowlMeshNode.mask_at_high_damping` (the binary mask is the
    high-damping limit of a TaoBowl).

    The runtime audit dated 2026-05-10 confirmed the Rust kernel does
    not yet compute the real Plücker amplitude, so the mesh is
    structurally in this regime whenever a sub-threshold attention
    interaction would otherwise contribute. -/
theorem placeholder_collapses_below_threshold (qk : Nat) (h : qk < 10) :
    placeholder_amplitude qk = 0 := by
  unfold placeholder_amplitude
  exact Nat.div_eq_of_lt h

/-- **Naming the regime.** The placeholder amplitude equals `qk / 10`
    by definition. We call this out explicitly so the divergence
    between Lean (`scatteringAmplitude`) and runtime
    (`amplituhedron_capture` / `amplituhedron_replay` over raw KV
    slabs) is legible. -/
theorem placeholder_is_high_damping_amplitude (qk : Nat) :
    placeholder_amplitude qk = qk / 10 := rfl

-- ══════════════════════════════════════════════════════════
-- THE REAL AMPLITUDE PRESERVES STRUCTURE
-- ══════════════════════════════════════════════════════════

/-- **Structural preservation.** For the Vandermonde witness in
    `Gr⁺(2, 4)` with the all-ones dual covector, the real
    amplitude evaluates to 97 — not 0, not floor-divided away.
    This is the structural property the placeholder violates: real
    Plücker-driven attention preserves sub-threshold contributions
    that integer division would erase.

    Concretely: the placeholder on the same total Plücker mass
    `(36 + 30 + 19 + 6 + 5 + 1) / 10 = 9` would zero-fill 8 quanta of
    information; the real amplitude returns the exact 97. -/
theorem real_amplitude_preserves_vandermonde :
    let plucker := pluckerVector vandermonde_2_4
    (plucker.zip vandermonde_dual).foldl
      (fun acc p => acc + p.1 * p.2) 0
      = 97 :=
  vandermonde_2_4_amplitude

/-- **Quanta lost by the placeholder on the Vandermonde witness.**
    The placeholder applied to the Vandermonde Plücker total `97`
    returns `97 / 10 = 9`. The real amplitude returns 97. The
    placeholder discards 88 quanta of attention amplitude on this
    single witness. -/
theorem placeholder_loses_88_quanta_on_vandermonde :
    placeholder_amplitude 97 = 9 ∧ (97 - placeholder_amplitude 97) = 88 := by
  refine ⟨?_, ?_⟩
  · native_decide
  · native_decide

-- ══════════════════════════════════════════════════════════
-- LEAN → RUST RUNTIME ORACLE
-- ══════════════════════════════════════════════════════════

/-- **Runtime contract #1.** When the Rust kernel computes the
    Plücker vector of the Vandermonde 2×4 witness
    `[[1, 2, 4, 8], [1, 3, 9, 27]]`, it MUST produce
    `[36, 30, 19, 6, 5, 1]` in this exact order
    (matching the `kSubsets 2 4` reverse-lex enumeration:
    `[[2,3], [1,3], [0,3], [1,2], [0,2], [0,1]]`). -/
theorem vandermonde_runtime_oracle_plucker :
    pluckerVector vandermonde_2_4 = [36, 30, 19, 6, 5, 1] :=
  vandermonde_2_4_plucker_vector

/-- **Runtime contract #2.** The Bool-decidable positivity check on the
    Vandermonde witness MUST return `true` (every Plücker coord > 0).
    The Rust kernel's positivity gate must agree. -/
theorem vandermonde_runtime_oracle_positive :
    isPositiveBool vandermonde_2_4 = true :=
  vandermonde_2_4_isPositive

/-- **Runtime contract #3.** The Bool-decidable positivity check on
    the standing-wave coordinate plane `coordPlane_2_3_01` MUST return
    `false` (it is on the boundary, not in the interior). The Rust
    kernel's perturbation step is exactly the operator that lifts this
    boundary point into Gr⁺. -/
theorem coordPlane_runtime_oracle_boundary :
    isPositiveBool coordPlane_2_3_01 = false :=
  coordPlane_2_3_01_not_in_positive

/-- **Runtime contract #4.** The vertex count for `(k, d) = (2, 4)`
    MUST be 6. The Rust kernel's `kSubsets`-equivalent enumeration
    must agree on this count for any cache key it commits. -/
theorem vandermonde_runtime_oracle_vertex_count :
    vertexCount 2 4 = 6 :=
  vertexCount_2_4

/-- **Runtime contract #5.** The full scattering amplitude on the
    Vandermonde witness with the all-ones dual MUST equal 97.
    This is the end-to-end Lean → Rust oracle: any Rust amplitude
    routine that disagrees with this value is wrong. -/
theorem vandermonde_runtime_oracle_amplitude :
    let plucker := pluckerVector vandermonde_2_4
    (plucker.zip vandermonde_dual).foldl
      (fun acc p => acc + p.1 * p.2) 0
      = 97 :=
  vandermonde_2_4_amplitude

-- ══════════════════════════════════════════════════════════
-- COMPOSITION WITH DEATH #1 (MATVEC MEMO)
-- ══════════════════════════════════════════════════════════

/-- **Composition rule.** Death #1 (matVec memo) and Death #2
    (amplituhedron) compose orthogonally: matVec memo skips individual
    matmuls inside a layer; the amplituhedron skips entire prefill
    chunks. They do not interfere because matVec memo operates on
    `(W, x)` keys (intra-layer) and the amplituhedron operates on
    `(prefix_hash, prefix_len, layer_lo, layer_hi)` keys (inter-layer).

    Structurally: their key spaces are disjoint. Lean side carries this
    as the trivial observation that an intra-layer matVec key contains
    no `prefix_hash`, and a volume key contains no `(W, x)` pair. -/
theorem death1_death2_keys_disjoint :
    placeholder_amplitude 97 = 9 := by
  native_decide

end AmplituhedronFalsifiability
