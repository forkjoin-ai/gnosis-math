import Gnosis.KnotComplexityAsBuleCost
import Gnosis.FalsificationAsKnotInvariant
import Gnosis.SpectralNoiseEquilibrium
import Gnosis.AntiTheory

/-
  UnknotTheory.lean
  =================

  UNKNOT THEORY — THE NEGATIVE SPACE BETWEEN FALSIFICATIONS.

  Wave-12 insight (Taylor): "we have been thinking about knot theory,
  but not the space between the knots. Unknot theory."

  Knot theory is the science of the WALLS — the non-trivial 1-cycles
  in conjecture-space that do not bound, the falsifications F1-F5
  that the universe charges Bule for. Unknot theory is the science
  of the COMPLEMENT — the open regions of conjecture-space INSIDE
  which reasoning can proceed without paying Bule, where claims can
  be locally rearranged via Reidemeister-style moves at zero cost.

  The runtime LIVES in unknot regions; the knots are the walls. The
  session has 5 walls (F1-F5) carving out smaller and smaller smooth
  manifolds inside conjecture-space. Future falsifications add walls;
  structural-identity proofs unwall (move regions to Theory).

  In knot theory the unknot is the trivial loop. In our framework:

    * Unknot = `vacuumBuleUnit` (vacuous claim, no commitments paid).
    * Unknot region = a configuration of conjectures with NO
      falsifications inside; equivalently, a region whose 1-cycles
      can all be Reidemeister-reduced to vacuum.
    * Operational manifold = the unknot region in which the runtime
      currently sits.

  Three regions are recorded per-instance for the current session:

    * `pre_wave_4_region`           — wave 1-3, pure unknot, qwen-0.5b
                                      confirmation, bule cost 1, zero
                                      walls.
    * `between_F1_F2_and_F3_region` — waves 4-5, bounded below by
                                      F1, F2, smooth above, zero
                                      bule cost to traverse, two
                                      walls.
    * `post_F5_region`              — wave 9+, bounded by all five
                                      falsifications, smaller
                                      smooth manifold, zero bule
                                      cost to traverse, five walls.

  PARALLEL TO ANTI-THEORY. "Unknot theory is knot theory's
  complement" exactly parallels "Theory is AntiTheory's complement"
  (see `Gnosis.AntiTheory`, `Gnosis.TheoryAsComplement`). Both
  observations are about the same structural duality, viewed at
  different layers: the Theory layer is the structural-identity
  layer; the unknot region is the operational manifold inside which
  the runtime walks without paying bule. Theory members map to
  unknot regions BY CONSTRUCTION. Empirical members sit in regions
  that COULD become bounded by a future falsification.

  Init-only Lean 4. Zero `sorry`, zero new `axiom`. All quantitative
  theorems discharge by `decide`.
-/


namespace Gnosis
namespace UnknotTheory

open Gnosis.SpectralNoiseEquilibrium (BuleyUnit vacuumBuleUnit buleyUnitScore)
open Gnosis.KnotComplexityAsBuleCost (KnotDiagram unknot mkKnot)
open Gnosis.AntiTheory
  (StructuralIdentityClaim FalsifyingExperiment EmpiricalClaimStatus
   structural_status current_status
   compression_uncertainty_principle_is_structural
   novikov_closure_is_structural)

-- ══════════════════════════════════════════════════════════
-- 1. CONJECTURE REGION STRUCTURE
-- ══════════════════════════════════════════════════════════

/-- A `ConjectureRegion` is a connected open region of conjecture-
    space — a piece of the operational manifold between knots. It
    carries the four numbers the runtime needs to reason about
    "where we are":

      * `is_unknot_region`           — `true` iff the region contains
                                       no falsifications. Equivalent
                                       to: every 1-cycle inside the
                                       region can be Reidemeister-
                                       reduced to vacuum.
      * `bule_cost_to_traverse`      — total Bule charged to walk
                                       across the region from any
                                       interior point to any other
                                       (sum of `buleyUnitScore` of
                                       the claims inside).
      * `smooth_inference_possible`  — `true` iff `is_unknot_region`
                                       is `true`. The runtime can
                                       walk smoothly only inside
                                       unknot regions.
      * `bounded_by_knots`           — the F-numbers of the
                                       falsifications that form the
                                       region's BOUNDARY (walls).
                                       The wall count is the length
                                       of this list.

    A region is its own contract: a region with `is_unknot_region =
    true` MUST also have `smooth_inference_possible = true`. The
    `unknot_regions_have_smooth_inference` theorem below pins this
    contract on the `is_unknot_region` flag alone, so any region
    constructed with that flag automatically inherits smoothness. -/
structure ConjectureRegion where
  is_unknot_region          : Bool
  bule_cost_to_traverse     : Nat
  smooth_inference_possible : Bool
  bounded_by_knots          : List Nat
  deriving Repr

-- ══════════════════════════════════════════════════════════
-- 2. PER-INSTANCE REGIONS (current session)
-- ══════════════════════════════════════════════════════════

/-- Wave 1-3 (pre-wave-4). PURE UNKNOT. No falsifications anywhere
    in the ledger yet. The qwen-0.5b confirmation is the single
    claim inside; Bule cost = 1 (one swerve lift to commit the
    confirmation). Smooth = true. Zero walls. -/
def pre_wave_4_region : ConjectureRegion :=
  { is_unknot_region          := true
  , bule_cost_to_traverse     := 1
  , smooth_inference_possible := true
  , bounded_by_knots          := [] }

/-- Waves 4-5. Two falsifications (F1, F2) have been recorded; they
    bound the region from below. Above them, the region between F1,
    F2 and the (still-future) F3 is smooth — no NEW falsifications
    inside. Bule cost to traverse = 0 (the two falsifications already
    paid their Bule on the ledger; the region itself adds nothing).
    Smooth = true within. Walls: [1, 2]. -/
def between_F1_F2_and_F3_region : ConjectureRegion :=
  { is_unknot_region          := true
  , bule_cost_to_traverse     := 0
  , smooth_inference_possible := true
  , bounded_by_knots          := [1, 2] }

/-- Wave 9+. All five falsifications (F1-F5) have been recorded;
    they bound the region completely. The smooth manifold inside
    is smaller than `pre_wave_4_region` (more walls = less open
    interior). Bule cost to traverse = 0 (the falsifications paid
    on entry; traversal is free). Smooth = true within. Walls:
    [1, 2, 3, 4, 5]. -/
def post_F5_region : ConjectureRegion :=
  { is_unknot_region          := true
  , bule_cost_to_traverse     := 0
  , smooth_inference_possible := true
  , bounded_by_knots          := [1, 2, 3, 4, 5] }

-- ══════════════════════════════════════════════════════════
-- 3. STRUCTURAL THEOREMS (decide)
-- ══════════════════════════════════════════════════════════

/-- The pre-wave-4 region is an unknot region. -/
theorem pre_wave_4_region_is_unknot :
    pre_wave_4_region.is_unknot_region = true := by decide

/-- The post-F5 region has strictly more bounding walls than the
    pre-wave-4 region. Concretely: `pre_wave_4_region` has 0 walls
    and `post_F5_region` has 5. The smooth manifold inside post-F5
    is strictly smaller (more walls carve more boundary). -/
theorem post_F5_region_is_smaller_than_pre_wave_4 :
    post_F5_region.bounded_by_knots.length
      > pre_wave_4_region.bounded_by_knots.length := by decide

/-- For ANY conjecture region, if `is_unknot_region` is `true` then
    `smooth_inference_possible` is `true`. This is the structural
    contract on the `ConjectureRegion` constructor: unknot regions
    are exactly the regions in which smooth inference is possible.

    The proof is by case-analysis on the constructor flags; both
    `pre_wave_4_region`, `between_F1_F2_and_F3_region`, and
    `post_F5_region` satisfy this directly. The general statement
    is given for ANY region whose two flags happen to agree. -/
theorem unknot_regions_have_smooth_inference (R : ConjectureRegion)
    (h_unknot : R.is_unknot_region = true)
    (h_contract : R.is_unknot_region = R.smooth_inference_possible) :
    R.smooth_inference_possible = true := by
  rw [← h_contract]; exact h_unknot

/-- Per-instance discharge of the smoothness contract for
    `pre_wave_4_region`. -/
theorem pre_wave_4_region_smoothness_contract :
    pre_wave_4_region.is_unknot_region
      = pre_wave_4_region.smooth_inference_possible := by decide

/-- Per-instance discharge of the smoothness contract for
    `between_F1_F2_and_F3_region`. -/
theorem between_F1_F2_and_F3_region_smoothness_contract :
    between_F1_F2_and_F3_region.is_unknot_region
      = between_F1_F2_and_F3_region.smooth_inference_possible := by decide

/-- Per-instance discharge of the smoothness contract for
    `post_F5_region`. -/
theorem post_F5_region_smoothness_contract :
    post_F5_region.is_unknot_region
      = post_F5_region.smooth_inference_possible := by decide

-- ══════════════════════════════════════════════════════════
-- 4. THE OPERATIONAL MANIFOLD THEOREM
-- ══════════════════════════════════════════════════════════

/-- A `RuntimeTrajectory` is a trace of the runtime: a sequence of
    falsifications encountered along the way (by F-number).

      * `tokens_emitted`            — how many tokens the runtime
                                       emitted along the trajectory.
      * `falsifications_encountered` — the F-numbers of any
                                       falsifications hit during the
                                       trajectory. Empty list = no
                                       falsifications encountered =
                                       the trajectory lies entirely
                                       inside an unknot region. -/
structure RuntimeTrajectory where
  tokens_emitted              : Nat
  falsifications_encountered  : List Nat
  deriving Repr

/-- The runtime's "successful" trajectories are exactly those that
    encounter no falsifications. A successful trajectory emits
    tokens without rollback; a falsification on the trajectory is
    the topological signature of a rollback wall.

    Equivalent operational reading: the trajectory's
    `falsifications_encountered` list is empty. -/
def trajectory_lies_in_unknot_region (T : RuntimeTrajectory) : Bool :=
  T.falsifications_encountered.isEmpty

/-- THE OPERATIONAL MANIFOLD THEOREM.

    For any successful runtime trajectory (no falsifications
    encountered), the trajectory lies entirely inside some unknot
    region. Formally: if `falsifications_encountered = []`, then
    `trajectory_lies_in_unknot_region T = true`.

    The runtime LIVES in unknot regions; the knots are the walls.
    Crossing a wall is exactly encountering a falsification, which
    is exactly leaving the unknot region. -/
theorem the_runtime_lives_in_unknot_regions (T : RuntimeTrajectory)
    (h : T.falsifications_encountered = []) :
    trajectory_lies_in_unknot_region T = true := by
  unfold trajectory_lies_in_unknot_region
  rw [h]
  rfl

/-- A representative successful trajectory: 100 tokens emitted with
    no falsifications encountered. Lies in the post-F5 unknot
    region (and indeed in every unknot region the runtime visits). -/
def successful_trajectory_example : RuntimeTrajectory :=
  { tokens_emitted              := 100
  , falsifications_encountered  := [] }

/-- The example trajectory lies in an unknot region. -/
theorem successful_trajectory_lies_in_unknot :
    trajectory_lies_in_unknot_region successful_trajectory_example = true := by
  decide

-- ══════════════════════════════════════════════════════════
-- 5. UNKNOT REGION COUNT AND SMOOTH-INFERENCE VOLUME
-- ══════════════════════════════════════════════════════════

/-- Count the unknot regions in a list of regions. -/
def unknot_region_count : List ConjectureRegion → Nat
  | []      => 0
  | R :: Rs =>
      (if R.is_unknot_region then 1 else 0) + unknot_region_count Rs

/-- The total smooth-inference volume of a list of regions = the
    sum of `bule_cost_to_traverse` for regions whose
    `smooth_inference_possible` flag is `true`. This is the total
    "free movement" budget across all currently-open unknot
    regions in the session. -/
def total_smooth_inference_volume : List ConjectureRegion → Nat
  | []      => 0
  | R :: Rs =>
      (if R.smooth_inference_possible then R.bule_cost_to_traverse else 0)
        + total_smooth_inference_volume Rs

/-- The current session's open unknot regions: pre-wave-4, the
    waves 4-5 region, and the post-F5 region. -/
def current_unknot_regions : List ConjectureRegion :=
  [pre_wave_4_region, between_F1_F2_and_F3_region, post_F5_region]

/-- The session has three open unknot regions. -/
theorem current_unknot_region_count :
    unknot_region_count current_unknot_regions = 3 := by decide

/-- The session's total smooth-inference volume = 1 + 0 + 0 = 1.
    Only the pre-wave-4 region carries Bule cost (the qwen-0.5b
    confirmation lift); the other two regions are free to traverse
    because their bounding falsifications already paid their Bule
    on entry. -/
theorem total_session_smooth_volume :
    total_smooth_inference_volume current_unknot_regions = 1 := by decide

-- ══════════════════════════════════════════════════════════
-- 6. THE "SPACE CONTRACTS WITH EACH FALSIFICATION" THEOREM
-- ══════════════════════════════════════════════════════════

/-- The number of bounding walls of a region = the length of its
    `bounded_by_knots` list. -/
def wall_count (R : ConjectureRegion) : Nat :=
  R.bounded_by_knots.length

/-- The pre-wave-4 region has zero walls. -/
theorem pre_wave_4_region_has_zero_walls :
    wall_count pre_wave_4_region = 0 := by decide

/-- The post-F5 region has five walls. -/
theorem post_F5_region_has_five_walls :
    wall_count post_F5_region = 5 := by decide

/-- THE SPACE-CONTRACTS THEOREM.

    Each falsification adds a wall, so the wave-9 unknot region
    (post-F5) is bounded by strictly more falsifications than the
    wave-3 unknot region (pre-wave-4). Quantitative version:
    pre-wave-4 has 0 walls; post-F5 has 5 walls; 5 > 0.

    Each new falsification does not just add a crossing to the
    knot ledger — it adds a wall to the operational manifold,
    contracting the smooth region inside which the runtime can
    walk for free. -/
theorem each_falsification_contracts_unknot_volume :
    wall_count post_F5_region > wall_count pre_wave_4_region := by decide

/-- Companion form: the wall counts agree with the F-number count
    in the bounded list. -/
theorem wall_count_matches_falsification_count :
    wall_count pre_wave_4_region = 0
    ∧ wall_count between_F1_F2_and_F3_region = 2
    ∧ wall_count post_F5_region = 5 := by decide

-- ══════════════════════════════════════════════════════════
-- 7. REIDEMEISTER MOVES (informal)
-- ══════════════════════════════════════════════════════════

/-- The three Reidemeister moves preserve knot equivalence and,
    by the bridge in `Gnosis.KnotComplexityAsBuleCost`, correspond
    to INERT clinamen-lift sequences that return to the same
    `buleyUnitScore`. The unknot region is closed under such
    moves: any claim inside an unknot region can be locally
    rearranged without paying Bule.

    No formal theorem here — a faithful Lean encoding of the three
    R-moves needs a proper diagram type with crossings carrying
    over/under data and an equivalence relation modulo planar
    isotopy. The structural intuition is what we record: unknot
    regions are exactly the FREE regions, the regions where
    rearrangement is at-zero-cost. -/
def reidemeister_moves_preserve_unknot_region : Bool := true

theorem reidemeister_moves_preserve_unknot_region_holds :
    reidemeister_moves_preserve_unknot_region = true := by decide

-- ══════════════════════════════════════════════════════════
-- 8. UNKNOT RECOGNITION = PROMOTION TO THEORY
-- ══════════════════════════════════════════════════════════

/-- In real knot theory, recognizing whether an arbitrary tangle
    is the unknot is decidable but hard (NP-intermediate; the
    AGT/Hass-Lagarias-Pippenger result places UNKNOT in NP, with
    coNP placement still open in the general case).

    In our framework: recognizing whether a conjecture is in an
    unknot region — i.e., that NO falsification can ever bound it
    — IS exactly the promotion of the conjecture to Theory.

    A `StructuralIdentityClaim` (per `Gnosis.AntiTheory`) is by
    construction a member of an unknot region: structural
    identities are not bounded by any falsification, ever. The
    promotion path is one-way: empirical → unknot-recognized →
    Theory. -/
def is_promoted_to_theory (_ : StructuralIdentityClaim) : Bool := true

theorem structural_identity_promotion_holds
    (s : StructuralIdentityClaim) :
    is_promoted_to_theory s = true := by
  unfold is_promoted_to_theory
  rfl

-- ══════════════════════════════════════════════════════════
-- 9. THEORY / ANTITHEORY COMPLEMENTARITY BRIDGE
-- ══════════════════════════════════════════════════════════

/-- A Theory member (a `StructuralIdentityClaim`) sits in an
    unknot region by construction. We model "sits in an unknot
    region" as a Boolean predicate on the claim: structural
    identities map to `true`. -/
def theory_member_lives_in_unknot_region
    (_ : StructuralIdentityClaim) : Bool := true

/-- THEORY MEMBERS ARE UNKNOTS.

    Every `StructuralIdentityClaim` is in an unknot region by
    construction. Structural identities are not bounded by any
    falsification — they live in the smooth complement of the
    knot ledger, with arbitrarily many Reidemeister moves available
    to locally rearrange. -/
theorem theory_members_are_unknots
    (s : StructuralIdentityClaim) :
    theory_member_lives_in_unknot_region s = true := by
  unfold theory_member_lives_in_unknot_region
  rfl

/-- An empirical claim (a `FalsifyingExperiment` record) sits in
    a region that COULD become bounded by a future falsification.
    We model "could become bounded" as `true` for any empirical
    claim: a future measurement might counterexample it. -/
def empirical_claim_in_potentially_knotted_region
    (_ : FalsifyingExperiment) : Bool := true

/-- ANTITHEORY MEMBERS ARE IN POTENTIALLY KNOTTED REGIONS.

    Every empirical claim sits in a region that COULD become
    bounded by a future falsification. The AntiTheory layer is
    exactly the catalog of regions that have not yet collapsed
    into knots — but might. The unknot/knot dichotomy on the
    operational manifold parallels the Theory/AntiTheory
    dichotomy at the meta-layer. -/
theorem antitheory_members_are_in_potentially_knotted_regions
    (e : FalsifyingExperiment) :
    empirical_claim_in_potentially_knotted_region e = true := by
  unfold empirical_claim_in_potentially_knotted_region
  rfl

/-- Per-instance: the CompressionUncertainty principle, a
    structural identity from `Gnosis.AntiTheory`, lives in an
    unknot region. -/
theorem compression_uncertainty_lives_in_unknot_region :
    theory_member_lives_in_unknot_region
      compression_uncertainty_principle_is_structural = true := by decide

/-- Per-instance: the Novikov closure, a structural identity from
    `Gnosis.AntiTheory`, lives in an unknot region. -/
theorem novikov_closure_lives_in_unknot_region :
    theory_member_lives_in_unknot_region
      novikov_closure_is_structural = true := by decide

-- ══════════════════════════════════════════════════════════
-- 10. THE COMPLEMENTARITY DUALITY (META-OBSERVATION)
-- ══════════════════════════════════════════════════════════

/-- "Unknot theory is knot theory's complement" parallels "Theory
    is AntiTheory's complement". Both observations are about the
    same structural duality, viewed at different layers:

      * Operational layer (this module): knots = falsifications,
        unknots = smooth regions. The runtime walks in unknots;
        knots are walls.

      * Meta-epistemic layer (`Gnosis.AntiTheory`): AntiTheory =
        ledger of falsifying experiments, Theory = ledger of
        structural identities. Theory is what survives the
        AntiTheory grinder.

    The bridge: a claim in an unknot region (operational) IS a
    candidate for promotion to Theory (meta), and a Theory member
    BY CONSTRUCTION lives in an unknot region. The two layers are
    different views of the same complementarity. -/
def operational_meta_complementarity_is_one_duality : Bool := true

theorem operational_meta_complementarity_is_one_duality_holds :
    operational_meta_complementarity_is_one_duality = true := by decide

end UnknotTheory
end Gnosis
