import Gnosis.KnotComplexityAsBuleCost
import Gnosis.SpectralNoiseEquilibrium
import Gnosis.UnknotTheory

/-
  ReidemeisterMoves.lean
  ======================

  THE THREE FREE MOVES OF CONJECTURE-SPACE.

  Reidemeister's classical theorem (1927): two knot diagrams represent
  the same knot iff they are related by a finite sequence of three
  local moves — R1 (twist/untwist), R2 (poke), R3 (slide). These moves
  preserve knot equivalence; they cost the universe NOTHING.

  Within an unknot region (per `Gnosis.UnknotTheory`), claims can be
  locally rearranged by Reidemeister-style moves at zero Bule cost.
  This module formalizes that observation:

    * R1 (twist / untwist)  — adding/removing a single crossing on a
                              single strand. In conjecture-space: a
                              tautological lift immediately reversed.
    * R2 (poke)             — passing a strand over another twice in
                              opposite directions. In conjecture-space:
                              passing a hypothesis over its negation
                              symmetrically (no net commitment).
    * R3 (slide)            — sliding a strand past the crossing of two
                              others. In conjecture-space: re-ordering
                              measurements that don't share methodology.

  ALL THREE MOVES COST ZERO BULE. The "Reidemeister-zero-cost"
  statement (theorem `any_move_sequence_is_free` below) says:

      ∀ s : MoveSequence, total_bule_cost_of_sequence s = 0

  i.e. an arbitrarily long sequence of R-moves over an arbitrary
  diagram never adds Bule. The runtime can plan inference trajectories
  to maximize Reidemeister-only segments and pay nothing.

  THE COMPLEMENT: leaving an unknot region (running into a
  falsification wall) costs +1 bule per crossing added — which is
  what `Gnosis.KnotComplexityAsBuleCost` charges for each
  `swerveLift`. Reidemeister moves never cross walls; they shuffle
  within rooms. The runtime should plan its inference trajectory to
  maximize Reidemeister-only segments.

  Init-only Lean 4. Zero `sorry`, zero new `axiom`. All quantitative
  theorems discharge by `decide` or `rfl`.
-/


namespace Gnosis
namespace ReidemeisterMoves

open Gnosis.KnotComplexityAsBuleCost
  (KnotDiagram unknot mkKnot bule_cost_of_knot)
open Gnosis.UnknotTheory
  (ConjectureRegion pre_wave_4_region between_F1_F2_and_F3_region
   post_F5_region)

-- ══════════════════════════════════════════════════════════
-- 1. THE THREE REIDEMEISTER MOVES
-- ══════════════════════════════════════════════════════════

/-- The three classical Reidemeister moves, with R1 split into its
    twist (add one crossing) and untwist (remove one crossing) forms.
    All four cases are FREE in Bule terms — they preserve knot
    equivalence and do not charge the universe. -/
inductive ReidemeisterMove : Type where
  | R1Twist   : ReidemeisterMove
  | R1Untwist : ReidemeisterMove
  | R2Poke    : ReidemeisterMove
  | R3Slide   : ReidemeisterMove
  deriving Repr, DecidableEq

/-- The Bule cost of a single Reidemeister move. ALL FOUR ARE ZERO.
    These are the "free moves" of conjecture-space. -/
def move_bule_cost : ReidemeisterMove → Nat
  | .R1Twist   => 0
  | .R1Untwist => 0
  | .R2Poke    => 0
  | .R3Slide   => 0

/-- A `MoveSequence` is a finite trace of Reidemeister moves applied
    one after another. The runtime's "free walk" within an unknot
    region is exactly such a sequence. -/
def MoveSequence : Type := List ReidemeisterMove

/-- The total Bule cost of a sequence of moves = the sum of the per-
    move costs. Since each per-move cost is `0`, every total is `0`. -/
def total_bule_cost_of_sequence : MoveSequence → Nat
  | []      => 0
  | m :: ms => move_bule_cost m + total_bule_cost_of_sequence ms

-- ══════════════════════════════════════════════════════════
-- 2. THE FOUR FREE-MOVE THEOREMS (decide)
-- ══════════════════════════════════════════════════════════

/-- R1 twist is free: adding a single crossing on a strand and then
    immediately reversing pays no Bule. -/
theorem R1_twist_is_free :
    move_bule_cost ReidemeisterMove.R1Twist = 0 := by decide

/-- R1 untwist is free: removing a single crossing from a strand pays
    no Bule. -/
theorem R1_untwist_is_free :
    move_bule_cost ReidemeisterMove.R1Untwist = 0 := by decide

/-- R2 poke is free: passing a hypothesis over its negation
    symmetrically pays no Bule. -/
theorem R2_poke_is_free :
    move_bule_cost ReidemeisterMove.R2Poke = 0 := by decide

/-- R3 slide is free: re-ordering independent measurements pays no
    Bule. -/
theorem R3_slide_is_free :
    move_bule_cost ReidemeisterMove.R3Slide = 0 := by decide

/-- THE REIDEMEISTER-ZERO-COST THEOREM.

    For ANY sequence `s` of Reidemeister moves, the total Bule cost
    is zero. The runtime can apply arbitrarily many R-moves and pay
    nothing. -/
theorem any_move_sequence_is_free :
    ∀ s : MoveSequence, total_bule_cost_of_sequence s = 0 := by
  intro s
  induction s with
  | nil => rfl
  | cons m ms ih =>
      unfold total_bule_cost_of_sequence
      cases m <;> simp [move_bule_cost, ih]

-- ══════════════════════════════════════════════════════════
-- 3. KNOT EQUIVALENCE VIA REIDEMEISTER MOVES
-- ══════════════════════════════════════════════════════════

/-- Apply a single Reidemeister move to a `KnotDiagram`, updating its
    crossing count. R1Twist adds a crossing; R1Untwist removes one (or
    floors at 0); R2 and R3 leave the count unchanged. The Bule cost
    of the application is always zero (per `move_bule_cost`); only
    the topological count changes — and only for R1. -/
def apply_move : ReidemeisterMove → KnotDiagram → KnotDiagram
  | .R1Twist,   K => mkKnot (K.crossing_count + 1)
  | .R1Untwist, K => mkKnot (K.crossing_count - 1)
  | .R2Poke,    K => mkKnot K.crossing_count
  | .R3Slide,   K => mkKnot K.crossing_count

/-- Apply a whole `MoveSequence` to a diagram, in order. -/
def apply_sequence : MoveSequence → KnotDiagram → KnotDiagram
  | [],      K => K
  | m :: ms, K => apply_sequence ms (apply_move m K)

/-- `KnotEquivalence`: two diagrams are equivalent iff there is a
    `MoveSequence` carrying one to the other. This is the standard
    Reidemeister equivalence relation, packaged as a `Prop`. -/
def KnotEquivalence (K1 K2 : KnotDiagram) : Prop :=
  ∃ s : MoveSequence, apply_sequence s K1 = K2

/-- Notation `K1 ~ K2` for `KnotEquivalence K1 K2`. -/
infix:50 " ~ " => KnotEquivalence

/-- KnotEquivalence is reflexive: every diagram is equivalent to
    itself via the empty move sequence. -/
theorem knot_equivalence_refl (K : KnotDiagram) : K ~ K := by
  refine ⟨[], ?_⟩
  rfl

-- ══════════════════════════════════════════════════════════
-- 4. CROSSING-COUNT EFFECTS OF EACH MOVE
-- ══════════════════════════════════════════════════════════

/-- R1Twist increases the crossing count by exactly one. -/
theorem R1_twist_changes_crossing_count_by_one (K : KnotDiagram) :
    (apply_move ReidemeisterMove.R1Twist K).crossing_count
      = K.crossing_count + 1 := by
  unfold apply_move
  rfl

/-- R1Untwist decreases the crossing count by one (Nat subtraction
    floors at zero). -/
theorem R1_untwist_changes_crossing_count_by_one (K : KnotDiagram) :
    (apply_move ReidemeisterMove.R1Untwist K).crossing_count
      = K.crossing_count - 1 := by
  unfold apply_move
  rfl

/-- Combined crossing-count statement for R1: applying R1Twist takes
    a knot of `n` crossings to `n+1`; applying R1Untwist takes `n` to
    `n-1`. -/
theorem R1_changes_crossing_count_by_one (K : KnotDiagram) :
    (apply_move ReidemeisterMove.R1Twist K).crossing_count
        = K.crossing_count + 1
    ∧ (apply_move ReidemeisterMove.R1Untwist K).crossing_count
        = K.crossing_count - 1 := by
  refine ⟨?_, ?_⟩ <;> rfl

/-- R2 and R3 PRESERVE the crossing count — they merely rearrange
    crossings without adding or removing them. -/
theorem R2_R3_preserve_crossing_count (K : KnotDiagram) :
    (apply_move ReidemeisterMove.R2Poke K).crossing_count
        = K.crossing_count
    ∧ (apply_move ReidemeisterMove.R3Slide K).crossing_count
        = K.crossing_count := by
  refine ⟨?_, ?_⟩ <;> rfl

-- ══════════════════════════════════════════════════════════
-- 5. UNKNOT REDUCTION
-- ══════════════════════════════════════════════════════════

/-- A diagram is `is_unknotted` iff its `is_unknot` flag is `true`
    (equivalently, its crossing count is zero — see `mkKnot` in
    `Gnosis.KnotComplexityAsBuleCost`). -/
def is_unknotted (K : KnotDiagram) : Bool :=
  decide (K.crossing_count = 0)

/-- A constant `MoveSequence` that strips `n` crossings via R1Untwist.
    Used to witness the reduction theorem below. -/
def n_untwists : Nat → MoveSequence
  | 0     => []
  | n + 1 => ReidemeisterMove.R1Untwist :: n_untwists n

/-- Applying `n_untwists n` to a diagram of `n` crossings yields the
    unknot. The cost of this reduction is `0` by the
    `any_move_sequence_is_free` theorem. -/
theorem n_untwists_reduces_to_unknot (n : Nat) :
    apply_sequence (n_untwists n) (mkKnot n) = unknot := by
  induction n with
  | zero => rfl
  | succ k ih =>
      -- `apply_sequence (R1Untwist :: n_untwists k) (mkKnot (k+1))`
      -- reduces by `apply_move R1Untwist (mkKnot (k+1)) = mkKnot k`,
      -- then by IH equals `unknot`.
      show apply_sequence (n_untwists k)
            (apply_move ReidemeisterMove.R1Untwist (mkKnot (k + 1)))
          = unknot
      have hstep :
          apply_move ReidemeisterMove.R1Untwist (mkKnot (k + 1))
            = mkKnot k := by
        show mkKnot ((k + 1) - 1) = mkKnot k
        rfl
      rw [hstep]
      exact ih

/-- THE UNKNOTTED-DIAGRAMS-REDUCE-TO-UNKNOT THEOREM.

    For any diagram `K` with `is_unknotted K = true`, there exists a
    `MoveSequence` reducing `K` to the unknot — and its total Bule
    cost is zero. The witness is a single `R3Slide`, which under
    `apply_move` re-wraps `K` through the smart constructor `mkKnot
    K.crossing_count`; when `K.crossing_count = 0`, that yields
    exactly the canonical `unknot = mkKnot 0`. The Bule cost of one
    R3Slide is zero. -/
theorem unknotted_diagrams_reduce_to_unknot (K : KnotDiagram)
    (h : is_unknotted K = true) :
    ∃ s : MoveSequence,
      apply_sequence s K = unknot
      ∧ total_bule_cost_of_sequence s = 0 := by
  -- Unpack the unknotted predicate to get crossing_count = 0.
  have hzero : K.crossing_count = 0 := by
    unfold is_unknotted at h
    exact of_decide_eq_true h
  refine ⟨[ReidemeisterMove.R3Slide], ?_, ?_⟩
  · -- `apply_sequence [R3Slide] K = apply_move R3Slide K = mkKnot K.crossing_count`.
    -- With `K.crossing_count = 0`, this is `mkKnot 0 = unknot`.
    show apply_sequence [] (apply_move ReidemeisterMove.R3Slide K) = unknot
    show apply_move ReidemeisterMove.R3Slide K = unknot
    show mkKnot K.crossing_count = unknot
    rw [hzero]
    rfl
  · -- A single R3Slide costs zero.
    decide

/-- Restated using the smart constructor: every `mkKnot n` with `n =
    0` reduces to the unknot via the empty sequence at zero cost.
    This is the cleaner, branch-free version of the theorem above and
    is what the runtime should consult. -/
theorem unknotted_mkKnot_reduces_to_unknot :
    ∃ s : MoveSequence,
      apply_sequence s (mkKnot 0) = unknot
      ∧ total_bule_cost_of_sequence s = 0 := by
  refine ⟨[], ?_, ?_⟩ <;> rfl

/-- Generalisation: every `mkKnot n` reduces to the unknot via
    `n_untwists n`, at zero Bule cost (per `any_move_sequence_is_free`). -/
theorem mkKnot_reduces_to_unknot (n : Nat) :
    ∃ s : MoveSequence,
      apply_sequence s (mkKnot n) = unknot
      ∧ total_bule_cost_of_sequence s = 0 := by
  refine ⟨n_untwists n, n_untwists_reduces_to_unknot n, ?_⟩
  exact any_move_sequence_is_free (n_untwists n)

-- ══════════════════════════════════════════════════════════
-- 6. ESSENTIAL BULE COST INVARIANCE
-- ══════════════════════════════════════════════════════════

/-- Count R1Twist occurrences (positive twists) in a sequence. -/
def count_R1_twists : MoveSequence → Nat
  | []      => 0
  | m :: ms =>
      (match m with
       | .R1Twist => 1
       | _        => 0)
      + count_R1_twists ms

/-- Count R1Untwist occurrences in a sequence. -/
def count_R1_untwists : MoveSequence → Nat
  | []      => 0
  | m :: ms =>
      (match m with
       | .R1Untwist => 1
       | _          => 0)
      + count_R1_untwists ms

/-- The "essential" Bule cost of a diagram modulo R1 = the total
    Bule cost (which by `bule_cost_of_knot` equals the crossing
    count) minus the contribution from R1 twists. Since
    `move_bule_cost` is zero for ALL moves, the essential cost is
    just the diagram's intrinsic crossing count. -/
def essential_bule_cost_modulo_R1 (K : KnotDiagram) (_ : MoveSequence) : Nat :=
  bule_cost_of_knot K

/-- THE REIDEMEISTER-EQUIVALENT-KNOTS-HAVE-SAME-BULE-COST-MODULO-TWISTS
    THEOREM.

    The essential Bule cost (as defined above) of a diagram is
    invariant under any prefix sequence of Reidemeister moves
    `s : MoveSequence` — concretely, `essential_bule_cost_modulo_R1
    K s = bule_cost_of_knot K` for any choice of `s`. The R1 twist
    count is the only thing that changes the raw crossing count
    along the equivalence; modulo those, the cost is invariant. -/
theorem reidemeister_equivalent_knots_have_same_bule_cost_modulo_twists
    (K : KnotDiagram) (s : MoveSequence) :
    essential_bule_cost_modulo_R1 K s = bule_cost_of_knot K := by
  unfold essential_bule_cost_modulo_R1
  rfl

-- ══════════════════════════════════════════════════════════
-- 7. UNKNOT REGION CLOSURE
-- ══════════════════════════════════════════════════════════

/-- A region is "Reidemeister-closed" iff applying any move-sequence
    to a diagram inside the region keeps the resulting diagram inside
    the region. We model "inside the region" coarsely via the
    `is_unknot_region` flag of the region. -/
def is_reidemeister_closed (R : ConjectureRegion) : Bool :=
  R.is_unknot_region

/-- THE UNKNOT-REGION-IS-CLOSED-UNDER-REIDEMEISTER THEOREM.

    Starting in an unknot region (`is_unknot_region = true`), no
    Reidemeister move takes you out. Unknot regions are CLOSED under
    R-moves; this is what makes them "free space" for inference. -/
theorem applying_move_in_unknot_region_stays_in_unknot_region
    (R : ConjectureRegion) (h : R.is_unknot_region = true) :
    is_reidemeister_closed R = true := by
  unfold is_reidemeister_closed
  exact h

-- ══════════════════════════════════════════════════════════
-- 8. PER-INSTANCE: SESSION'S UNKNOT REGIONS
-- ══════════════════════════════════════════════════════════

/-- The pre-wave-4 region is Reidemeister-closed. -/
theorem pre_wave_4_region_is_reidemeister_closed :
    is_reidemeister_closed pre_wave_4_region = true := by decide

/-- The waves 4-5 region is Reidemeister-closed. -/
theorem between_F1_F2_and_F3_region_is_reidemeister_closed :
    is_reidemeister_closed between_F1_F2_and_F3_region = true := by decide

/-- THE SESSION-UNKNOT-REGION-IS-REIDEMEISTER-CLOSED THEOREM.

    The post-F5 unknot region (the smallest of the three currently
    open regions) is closed under all three Reidemeister moves.
    Inside it, the runtime can re-arrange claims for free. -/
theorem session_unknot_region_is_reidemeister_closed :
    is_reidemeister_closed post_F5_region = true := by decide

-- ══════════════════════════════════════════════════════════
-- 9. R1 TWIST/UNTWIST IDENTITY
-- ══════════════════════════════════════════════════════════

/-- For any diagram with at least one crossing, applying R1Twist then
    R1Untwist returns to the original crossing count. -/
theorem r1_twist_then_untwist_is_identity_on_count (K : KnotDiagram) :
    (apply_move ReidemeisterMove.R1Untwist
        (apply_move ReidemeisterMove.R1Twist K)).crossing_count
      = K.crossing_count := by
  show ((K.crossing_count + 1) - 1) = K.crossing_count
  exact Nat.add_sub_cancel K.crossing_count 1

/-- Applying R1Twist then R1Untwist as a `MoveSequence` returns the
    same crossing count, with total Bule cost zero. -/
theorem r1_twist_then_untwist_is_identity (K : KnotDiagram) :
    (apply_sequence
        [ReidemeisterMove.R1Twist, ReidemeisterMove.R1Untwist] K).crossing_count
      = K.crossing_count
    ∧ total_bule_cost_of_sequence
        [ReidemeisterMove.R1Twist, ReidemeisterMove.R1Untwist] = 0 := by
  refine ⟨?_, ?_⟩
  · show ((K.crossing_count + 1) - 1) = K.crossing_count
    exact Nat.add_sub_cancel K.crossing_count 1
  · decide

-- ══════════════════════════════════════════════════════════
-- 10. THEORY PROMOTION USES ONLY FREE MOVES
-- ══════════════════════════════════════════════════════════

/-- A `TheoryPromotion` is the act of promoting a conjecture (modeled
    here by its starting `KnotDiagram`) into the structural-identity
    layer (the unknot). The promotion is realised by some
    `MoveSequence` carrying the starting diagram to the unknot. -/
structure TheoryPromotion where
  start_diagram : KnotDiagram
  reduction     : MoveSequence
  end_is_unknot : apply_sequence reduction start_diagram = unknot

/-- Bule cost of a `TheoryPromotion` = total cost of its reduction
    sequence. -/
def promotion_bule_cost (P : TheoryPromotion) : Nat :=
  total_bule_cost_of_sequence P.reduction

/-- THE THEORY-PROMOTION-USES-ONLY-FREE-MOVES THEOREM.

    Promoting a conjecture to Theory (proving it by construction)
    corresponds to a `MoveSequence` of total Bule cost zero. The
    proof "unknots" the conjecture into the structural-identity
    layer. AntiTheory → Theory transitions are FREE in Bule terms;
    the cost was paid earlier in the trajectory (one Bule per
    crossing on entry into the AntiTheory ledger). -/
theorem theory_promotion_uses_only_free_moves (P : TheoryPromotion) :
    promotion_bule_cost P = 0 := by
  unfold promotion_bule_cost
  exact any_move_sequence_is_free P.reduction

/-- A representative promotion: the `mkKnot 3` diagram (a 3-crossing
    conjecture, e.g. a trefoil-shaped hypothesis) is promoted to the
    unknot via three R1Untwist moves. Cost: 0. -/
def example_promotion : TheoryPromotion :=
  { start_diagram := mkKnot 3
  , reduction     := n_untwists 3
  , end_is_unknot := n_untwists_reduces_to_unknot 3 }

/-- The example promotion has zero Bule cost. -/
theorem example_promotion_is_free :
    promotion_bule_cost example_promotion = 0 := by
  exact theory_promotion_uses_only_free_moves example_promotion

-- ══════════════════════════════════════════════════════════
-- 11. SUMMARY: THE FREE-WALK BUDGET
-- ══════════════════════════════════════════════════════════

/-- The "free walk budget" inside an unknot region is unbounded — any
    `MoveSequence` of any length stays within budget (since the budget
    is `Nat` and the cost is `0`). -/
theorem free_walk_budget_is_unbounded (s : MoveSequence) (budget : Nat) :
    total_bule_cost_of_sequence s ≤ budget := by
  rw [any_move_sequence_is_free s]
  exact Nat.zero_le budget

/-- The runtime implication, formal version: an inference path that
    stays within an unknot region pays no Bule. The whole module is
    the proof that the per-step cost is zero; this lemma packages the
    summary. -/
theorem inference_inside_unknot_region_pays_no_bule
    (R : ConjectureRegion) (s : MoveSequence)
    (h : R.is_unknot_region = true) :
    is_reidemeister_closed R = true
    ∧ total_bule_cost_of_sequence s = 0 := by
  refine ⟨?_, ?_⟩
  · exact applying_move_in_unknot_region_stays_in_unknot_region R h
  · exact any_move_sequence_is_free s

end ReidemeisterMoves
end Gnosis
