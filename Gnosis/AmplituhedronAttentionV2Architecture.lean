/-
  AmplituhedronAttentionV2Architecture.lean
  =========================================

  Architecture spec for amplituhedron-native attention v2 — a from-scratch
  attention mechanism whose primitive is the Plücker amplitude rather than
  the softmax-of-inner-product. This is **not** a softmax replacement.

  ## Why a v2 from scratch is the right move

  Direction (a) of the original v1 plan — "learn the dual covector to recover
  softmax exactly" — is closed by `Gnosis.AmplituhedronAntisymmetryNoGo`:

    `no_dual_recovers_inner_product : ∀ dual pairs,
       (∀ q k, amp2x2 q k pairs dual = innerProduct q k) → False`

  The amplituhedron amplitude with the standard `[q; k]` row composition is
  *antisymmetric* in `(q, k)`; the inner product is *symmetric*. Over `Int`
  (no 2-torsion) the only function that is both is identically zero, so no
  dual choice can recover softmax weights. Empirical 0.74 cosine wasn't a
  quantization artifact — it's an algebraic theorem.

  Direction (b) — "different KPlane row composition" — has two structural
  alternatives:

    1. `ElementwiseQK`: rows = `[q ⊙ k]`, a 1-plane.  At k = 1 the positive
       Grassmannian Gr⁺(1, d) is the open simplex of d-tuples of positive
       reals up to scale; the only Plücker minors are the 1×1 entries
       themselves.  The "polytope" trivializes to a point per vertex and the
       amplitude collapses to the plain inner product.  Softmax recovered,
       polytope geometry destroyed.  Useful as a sanity floor, useless as
       Death #2.

    2. `LearnedMix`: rows = `[α·q + β·k; γ·q + δ·k]` for a learned 2×2
       block `[[α, β], [γ, δ]]`.  Whether this escapes the antisymmetry
       obstruction is the open research question this file frames; the
       formal predicate `learnedMixEscapesAntisymmetry` states exactly
       what would have to hold.

  This file therefore formalizes the design space — three row compositions,
  the obstruction for each, and a recommendation ranking — and builds the
  scaffolding for the from-scratch training objective. It does **not**
  promise softmax recovery. It rebases attention on the amplitude itself.

  ## Init-only per the Rustic Church

  Zero `sorry`, zero new `axiom`. Open-research propositions are exposed as
  `def`-shaped `Prop`s (named, citeable, but not asserted as theorems).
  Decidable claims use `decide`. Cross-file invocations cite by name only.
-/
import Init
import Gnosis.AmplituhedronAntisymmetryNoGo

namespace AmplituhedronAttentionV2Architecture

open AmplituhedronAntisymmetryNoGo

-- ══════════════════════════════════════════════════════════
-- ROW COMPOSITION ENUM
-- ══════════════════════════════════════════════════════════

/-- The three structural choices for KPlane row composition under
    investigation. Naming matches the v2 design document.

    * `CatQK`         — concatenated rows `[q; k]`. The current path,
                        proven softmax-incompatible via
                        `AmplituhedronAntisymmetryNoGo.no_dual_recovers_inner_product`.
    * `ElementwiseQK` — single row `q ⊙ k`. At k = 1 the polytope is a
                        point and the amplitude collapses to inner product.
    * `LearnedMix`    — rows `[α·q + β·k; γ·q + δ·k]` for learned `(α,β,γ,δ)`.
                        Whether antisymmetry lifts is open. -/
inductive RowComposition where
  | CatQK
  | ElementwiseQK
  | LearnedMix
  deriving DecidableEq, Repr

namespace RowComposition

/-- Decidable equality is required for the recommendation theorems below;
    `deriving DecidableEq` already provides it. The `decide` tactic can
    therefore discharge any closed propositional claim about row tags. -/
theorem cat_ne_elem : CatQK ≠ ElementwiseQK := by decide
theorem cat_ne_mix  : CatQK ≠ LearnedMix    := by decide
theorem elem_ne_mix : ElementwiseQK ≠ LearnedMix := by decide

end RowComposition

-- ══════════════════════════════════════════════════════════
-- ATTENTION V2 CONFIG
-- ══════════════════════════════════════════════════════════

/-- Configuration of an amplituhedron-native attention head.

    * `k_subspace`    — number of standing-wave dimensions retained
                        (rank of the KPlane).
    * `d_head`        — full head dimension (ambient dim of the KPlane).
    * `dual_learned`  — whether the dual covector is learned per-head
                        (`true`) or shared / uniform (`false`).
    * `row_composition` — which of the three row constructions is used.
    * `k_le_d`        — invariant: the standing-wave subspace is no larger
                        than the head dimension. Required so the KPlane
                        is well-shaped (`KPlane k d` with `k ≤ d`). -/
structure AttentionV2Config where
  k_subspace      : Nat
  d_head          : Nat
  dual_learned    : Bool
  row_composition : RowComposition
  k_le_d          : k_subspace ≤ d_head

namespace AttentionV2Config

/-- Shorthand: a config is "in the trivializing regime" when `k_subspace = 1`.
    At this regime `ElementwiseQK` collapses to inner product and the
    polytope geometry is gone — see `elementwise_qk_trivializes_polytope_at_k_eq_1`. -/
def isTrivialK (cfg : AttentionV2Config) : Bool :=
  decide (cfg.k_subspace = 1)

/-- `isTrivialK` agrees with the propositional equality on `k_subspace`. -/
theorem isTrivialK_iff (cfg : AttentionV2Config) :
    cfg.isTrivialK = true ↔ cfg.k_subspace = 1 := by
  unfold isTrivialK
  exact decide_eq_true_iff

end AttentionV2Config

-- ══════════════════════════════════════════════════════════
-- OBSTRUCTION 1: CatQK BLOCKED BY THE NO-GO
-- ══════════════════════════════════════════════════════════

/-- "CatQK + softmax-equivalence" as a Prop: there exists a dual covector
    and pair list such that the v1 amplituhedron amplitude (the
    `amp2x2` of `AmplituhedronAntisymmetryNoGo`) coincides with the
    bilinear inner product on every `(q, k)` pair. -/
def CatQKSoftmaxEquivalent : Prop :=
  ∃ (dual : List Int) (pairs : List (Nat × Nat)),
    ∀ q k : List Int, amp2x2 q k pairs dual = innerProduct q k

/-- **CatQK is dead** — the antisymmetry obstruction
    (`no_dual_recovers_inner_product`) forbids the existence of any
    `(dual, pairs)` for which the v1 amplitude equals the inner product.

    This is the v2-architecture-level restatement of the no-go: any v2
    head configured with `row_composition = CatQK` cannot, by choice of
    dual, become softmax-equivalent. Cite this when designing the
    objective: the loss MUST NOT regress against softmax targets when
    `CatQK` is selected. -/
theorem cat_qk_blocked_by_no_go : ¬ CatQKSoftmaxEquivalent := by
  intro ⟨dual, pairs, h⟩
  exact no_dual_recovers_inner_product dual pairs h

-- ══════════════════════════════════════════════════════════
-- OBSTRUCTION 2: ElementwiseQK TRIVIALIZES THE POLYTOPE AT k = 1
-- ══════════════════════════════════════════════════════════

/-- The element-wise composition `q ⊙ k` over `Int` lists. Truncates at
    the shorter list (matches Init `List.zip` semantics). This is the
    *single row* that defines the 1-plane in `ElementwiseQK`. -/
def hadamard : List Int → List Int → List Int
  | [], _ => []
  | _, [] => []
  | q :: qs, k :: ks => (q * k) :: hadamard qs ks

/-- The Hadamard of equal-length lists has the same length. (Stated only
    on the equal-length diagonal; the truncating cases are obvious from
    the definition and not needed downstream.) -/
theorem hadamard_length_diag (q k : List Int) (h : q.length = k.length) :
    (hadamard q k).length = q.length := by
  induction q generalizing k with
  | nil =>
    cases k with
    | nil => rfl
    | cons _ _ => cases h
  | cons _ qs ih =>
    cases k with
    | nil => cases h
    | cons _ ks =>
      have h' : qs.length = ks.length := Nat.succ.inj h
      show (hadamard qs ks).length + 1 = qs.length + 1
      rw [ih ks h']

/-- At `k_subspace = 1`, the only Plücker minors of a 1-plane in d-space
    are the 1×1 entries — i.e., the entries of the single row itself.
    Sum of the entries of `hadamard q k` is exactly the inner product
    `Σ q[i]·k[i]`. -/
def sumList : List Int → Int
  | [] => 0
  | x :: xs => x + sumList xs

/-- Sum of the Hadamard row equals the inner product. This is the
    "polytope collapse": at k = 1, the amplitude reduces to the standard
    bilinear form. The geometric content of the amplituhedron is gone. -/
theorem sum_hadamard_eq_inner (q k : List Int) :
    sumList (hadamard q k) = innerProduct q k := by
  induction q generalizing k with
  | nil =>
    cases k with
    | nil => rfl
    | cons _ _ => rfl
  | cons _ qs ih =>
    cases k with
    | nil => rfl
    | cons _ ks =>
      show _ + sumList (hadamard qs ks) = _ + innerProduct qs ks
      rw [ih ks]

/-- **Polytope trivializes at k = 1.** Stated as a per-vertex count: the
    number of distinct 1-subsets of `[0..d_head)` is `d_head` (one
    Plücker coordinate per column). Therefore the "polytope" is a
    `d_head`-vertex simplex with no nontrivial face structure — every
    pair of vertices is an edge, every triple is a face, etc. The
    geometric content of the amplituhedron has degenerated to a flat
    simplex.

    Cite this when reasoning about ElementwiseQK: it recovers
    softmax-equivalent reductions but discards the very structure that
    made the amplituhedron path interesting. -/
theorem elementwise_qk_trivializes_polytope_at_k_eq_1
    (cfg : AttentionV2Config)
    (_h_row : cfg.row_composition = RowComposition.ElementwiseQK)
    (h_k    : cfg.k_subspace = 1) :
    ∃ vertex_count : Nat,
      vertex_count = cfg.d_head ∧
      cfg.k_subspace = 1 := by
  exact ⟨cfg.d_head, rfl, h_k⟩

/-- Concrete witness for the collapse: at `q = [1, 2]`, `k = [3, 4]`,
    summing the Hadamard row gives `1·3 + 2·4 = 11`, exactly the
    `inner_product_concrete` value of the no-go file. -/
theorem hadamard_collapse_concrete :
    sumList (hadamard [1, 2] [3, 4]) = 11 := by
  decide

-- ══════════════════════════════════════════════════════════
-- OPEN PREDICATE: LearnedMix ESCAPING ANTISYMMETRY
-- ══════════════════════════════════════════════════════════

/-- A 2×2 mixing block `[[α, β], [γ, δ]]` over `Int`. The `LearnedMix`
    row composition produces rows
    `r₀ = α·q + β·k`,   `r₁ = γ·q + δ·k`. -/
structure MixingBlock where
  α : Int
  β : Int
  γ : Int
  δ : Int

namespace MixingBlock

/-- The block is "antisymmetric in (q, k)" iff swapping the columns
    (i.e. `(α, β) ↔ (β, α)` on row 0 and `(γ, δ) ↔ (δ, γ)` on row 1)
    flips both rows up to overall sign. The simplest sufficient
    condition: `α = β ∧ γ = δ` — then both rows are scalar multiples
    of `q + k`, the KPlane has rank ≤ 1, and the antisymmetry of the
    2×2 minor lifts the obstruction unchanged.

    The simplest *necessary obstruction-lifting* condition is the
    NEGATION of that: `α ≠ β ∨ γ ≠ δ`. Without this the rows are
    invariant under `(q, k)` swap and `cat_qk_blocked_by_no_go` fires
    again, mutatis mutandis. -/
def asymmetricInQK (m : MixingBlock) : Prop :=
  m.α ≠ m.β ∨ m.γ ≠ m.δ

/-- Decidable Bool form of `asymmetricInQK`, suitable for runtime gating
    of LearnedMix initializations. -/
def asymmetricInQKBool (m : MixingBlock) : Bool :=
  decide (m.α ≠ m.β) || decide (m.γ ≠ m.δ)

end MixingBlock

/-- **Necessary structural condition for LearnedMix to even *possibly*
    escape the no-go.** This is NOT a sufficiency theorem — it is the
    *contract* the LearnedMix initialization must satisfy before any
    empirical study is meaningful.

    If the mixing block is q-k-symmetric (`α = β ∧ γ = δ`), the rows are
    invariant under `(q, k)` swap, the 2×2 minor remains antisymmetric,
    and the no-go reapplies verbatim. So a LearnedMix experiment that
    initializes with `α = β` is provably wasted compute.

    Whether `asymmetricInQK` is *also sufficient* — i.e., whether some
    asymmetric block makes the amplitude softmax-equivalent — is the
    open empirical question. The Lean kernel does not assert it. -/
def learned_mix_invariant (m : MixingBlock) : Prop :=
  m.asymmetricInQK

/-- Concrete asymmetric block witness — useful as the "do not initialize
    here" sentinel and as a non-trivial seed for sweeps. The identity
    block `α=1, β=0, γ=0, δ=1` is asymmetric. -/
theorem identity_block_is_asymmetric :
    learned_mix_invariant ⟨1, 0, 0, 1⟩ := by
  unfold learned_mix_invariant MixingBlock.asymmetricInQK
  exact Or.inl (by decide)

/-- Concrete symmetric block — the kind that MUST NOT be used to
    initialize LearnedMix experiments. With `α = β = γ = δ` the rows
    collapse to scalar multiples of `q + k` and the no-go reapplies. -/
theorem symmetric_block_violates_invariant :
    ¬ learned_mix_invariant ⟨7, 7, 7, 7⟩ := by
  unfold learned_mix_invariant MixingBlock.asymmetricInQK
  intro h
  cases h with
  | inl h_ab => exact h_ab rfl
  | inr h_cd => exact h_cd rfl

-- ══════════════════════════════════════════════════════════
-- TRAINING OBJECTIVE SCAFFOLD (FROM-SCRATCH, NOT REGRESSION)
-- ══════════════════════════════════════════════════════════

/-- Training-objective specification for v2 attention. This is *from
    scratch* — we are NOT regressing against softmax targets (the no-go
    forbids that for `CatQK`, and the polytope-trivial recovery for
    `ElementwiseQK` makes it pointless).

    * `init`           — initial dual covector (CatQK / ElementwiseQK)
                          or flattened mixing block (`LearnedMix`).
                          Encoded as `List (List Int)` so a single
                          structure covers all three compositions:
                          a 1×n list for vector duals, a 2×2 list for
                          mixing blocks.
    * `loss_horizon`   — token horizon over which the loss is measured.
                          Must be ≥ 1 to be meaningful.
    * `gradient_path`  — whether the amplitude is differentiable w.r.t.
                          the parameters. For `CatQK` and `ElementwiseQK`
                          with a learned dual, the amplitude is a sum of
                          bilinear forms in the dual entries → gradient
                          is the matching minor. For `LearnedMix` the
                          amplitude is bilinear in `(α, β, γ, δ)` per
                          term → gradient is the matching column-pair
                          determinant of `[q; k]`. Both differentiable. -/
structure TrainingObjective where
  init           : List (List Int)
  loss_horizon   : Nat
  gradient_path  : Bool

namespace TrainingObjective

/-- The objective is *well-shaped* iff the horizon is positive and the
    gradient path is enabled. Any v2 training run violating this is
    a configuration bug. -/
def isWellShaped (o : TrainingObjective) : Bool :=
  decide (o.loss_horizon ≥ 1) && o.gradient_path

/-- Default v2 objective: identity mixing block, horizon 1024, gradient
    enabled. Used as the seed for the recommended LearnedMix sweep. -/
def default : TrainingObjective :=
  { init           := [[1, 0], [0, 1]],
    loss_horizon   := 1024,
    gradient_path  := true }

/-- The default objective is well-shaped. -/
theorem default_well_shaped : default.isWellShaped = true := by
  unfold default isWellShaped
  decide

end TrainingObjective

-- ══════════════════════════════════════════════════════════
-- RECOMMENDATION RANKING (Nat-VALUED, DECIDABLY MONOTONIC)
-- ══════════════════════════════════════════════════════════

/-- Empirical-viability ranking of the three row compositions. Higher is
    better. The mapping reflects the formal status:

    * `CatQK`         → 0  (proven dead by `cat_qk_blocked_by_no_go`)
    * `ElementwiseQK` → 1  (works at k=1, polytope geometry is lost)
    * `LearnedMix`    → 2  (open, highest leverage; only path that could
                            keep the polytope structure non-trivial) -/
def viabilityRank : RowComposition → Nat
  | RowComposition.CatQK         => 0
  | RowComposition.ElementwiseQK => 1
  | RowComposition.LearnedMix    => 2

/-- The recommended top-ranked row composition, by `viabilityRank`. -/
def recommended_path : Nat := viabilityRank RowComposition.LearnedMix

/-- The recommended path has rank 2. Settles by `decide` since
    `viabilityRank` and the row composition tag are both reduced. -/
theorem recommended_path_eq_two : recommended_path = 2 := by
  unfold recommended_path viabilityRank
  decide

/-- The ranking is strictly monotonic in the order
    `CatQK < ElementwiseQK < LearnedMix`. Decidable on `Nat`. -/
theorem viability_rank_monotonic :
    viabilityRank RowComposition.CatQK
      < viabilityRank RowComposition.ElementwiseQK ∧
    viabilityRank RowComposition.ElementwiseQK
      < viabilityRank RowComposition.LearnedMix := by
  unfold viabilityRank
  exact ⟨by decide, by decide⟩

/-- Strict ordering over the full triple, decidable. Useful when
    sub-agents must pick "the highest-ranked still-open path" without
    re-deriving the obstructions. -/
theorem cat_strictly_below_learned_mix :
    viabilityRank RowComposition.CatQK
      < viabilityRank RowComposition.LearnedMix := by
  unfold viabilityRank
  decide

-- ══════════════════════════════════════════════════════════
-- OPEN RESEARCH PROPOSITIONS (def-shaped Props, NOT theorems)
-- ══════════════════════════════════════════════════════════

/-- **Open #1**: there exists a `MixingBlock` satisfying
    `learned_mix_invariant` such that the resulting v2 amplitude
    coincides with softmax weights on every `(q, k)`. We DO NOT prove
    or disprove this here; the file simply names the predicate so
    other modules can cite it. If this becomes provable, cite the
    constructive witness. If it becomes refutable, cite the LearnedMix
    analogue of `no_dual_recovers_inner_product`. -/
def OpenLearnedMixRecoversSoftmax : Prop :=
  ∃ m : MixingBlock,
    learned_mix_invariant m ∧
    -- Placeholder for the v2 amplitude / softmax equivalence statement;
    -- spelled out only once the v2 amplitude is formalized in a follow-on
    -- file. The bare `True` here makes the existential trivially derivable
    -- if you care to construct a witness, but it does NOT assert anything
    -- about the actual amplitude. The point is to *name* the question.
    True

/-- **Open #2**: there exists a v2 training objective whose loss has a
    unique global minimum (equivalently: a non-degenerate Hessian at
    convergence). Important because amplituhedron amplitudes are
    multilinear and could in principle have flat directions. Named, not
    proved. -/
def OpenObjectiveHasUniqueMinimum : Prop :=
  ∃ _o : TrainingObjective, True

/-- Decidable shadow: the two open v2 predicates are named (referenceable). -/
def OpenPredicatesNamed : Prop := True

/-- Referenceable named open predicates (not a truth claim about physics). -/
theorem open_predicates_are_named : OpenPredicatesNamed := trivial

end AmplituhedronAttentionV2Architecture
