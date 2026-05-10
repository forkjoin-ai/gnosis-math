/-
  StrictRefinementLatticePattern.lean
  ===================================

  Cross-pollination Pattern D: strict predicate refinement.

  The prior pattern modules captured three reusable shapes:

  * `RetractLatticePattern` - forget-and-recover on a reachable subset.
  * `HomomorphismLatticePattern` - lift while preserving an invariant.
  * `AxisCardinalityFoldPattern` - coordinate growth as a product fold.

  This module closes the remaining loose thread from the audit:
  a higher-resolution predicate is a genuine refinement of a coarser
  predicate when every narrow witness is broad, but some broad witness
  is not narrow.

  Concrete instances:

  * Skyrms forward fixedness is strictly broader than Buley
    bulk-Novikov closure.
  * All `TaoBowl` values are strictly broader than the reachable
    sub-lattice carved out by `bowlOfField`.
  * All richer `EmotionPhenomenon` values are strictly broader than
    the single-cell representable fragment.

  Zero `sorry`, zero new `axiom`.
-/

import Gnosis.BuleyErgodicClosure
import Gnosis.ThoughtBowlMechanicsRefined
import Gnosis.AffectMatrixCompleteness

namespace StrictRefinementLatticePattern

open SkyrmsUltraLongRunEquilibrium (PolarizationState)

/-! ## Abstract strict predicate refinement -/

/-- A strict predicate refinement on a shared carrier type.

    `narrow` refines `broad` when every narrow witness is broad, and
    the refinement is strict when at least one broad witness lies
    outside the narrow predicate. -/
structure StrictPredicateRefinement (A : Type) where
  broad : A → Prop
  narrow : A → Prop
  narrow_implies_broad : ∀ a, narrow a → broad a
  strict_witness : ∃ a, broad a ∧ ¬ narrow a

/-- The gap packaged by a strict refinement. -/
theorem StrictPredicateRefinement.gap
    {A : Type} (R : StrictPredicateRefinement A) :
    ∃ a, R.broad a ∧ ¬ R.narrow a :=
  R.strict_witness

/-- A strict refinement rules out equivalence of the two predicates. -/
theorem StrictPredicateRefinement.not_equivalent
    {A : Type} (R : StrictPredicateRefinement A) :
    ¬ (∀ a, R.broad a ↔ R.narrow a) := by
  intro h
  obtain ⟨a, haBroad, haNotNarrow⟩ := R.strict_witness
  exact haNotNarrow ((h a).mp haBroad)

/-! ## Instance 1: Skyrms broadness vs Buley closure -/

/-- Pattern D for the equilibrium ladder: forward fixedness is the
    broad Skyrms predicate; bulk-Novikov closure is the narrow Buley
    predicate. -/
def skyrmsBuleyStrictRefinement :
    StrictPredicateRefinement PolarizationState where
  broad := fun s => BuleyErgodicClosure.forwardStep s = s
  narrow := BuleyErgodicClosure.IsBulkNovikovClosed
  narrow_implies_broad := fun _ h => h.2
  strict_witness := BuleyErgodicClosure.skyrms_admits_more_fixed_points_than_buley

/-- The existing Skyrms-vs-Buley separator factors through
    `StrictPredicateRefinement.gap`. -/
theorem skyrms_admits_more_fixed_points_than_buley_via_refinement :
    ∃ s : PolarizationState,
      BuleyErgodicClosure.forwardStep s = s ∧
      ¬ BuleyErgodicClosure.IsBulkNovikovClosed s :=
  skyrmsBuleyStrictRefinement.gap

/-- Forward fixedness and bulk-Novikov closure are not equivalent
    predicates on `PolarizationState`. -/
theorem skyrms_forward_fixed_not_equivalent_to_buley_closed :
    ¬ (∀ s : PolarizationState,
        BuleyErgodicClosure.forwardStep s = s ↔
        BuleyErgodicClosure.IsBulkNovikovClosed s) :=
  skyrmsBuleyStrictRefinement.not_equivalent

/-! ## Instance 2: all bowls vs reachable bowls -/

/-- Pattern D for bowl mechanics: all `TaoBowl` values form the broad
    type-level space; `IsReachable` carves the strict sub-lattice
    that has a canonical thought-field preimage. -/
def taoBowlReachabilityStrictRefinement :
    StrictPredicateRefinement EchoChamberAsTaoBowl.TaoBowl where
  broad := fun _ => True
  narrow := ThoughtBowlMechanicsRefined.IsReachable
  narrow_implies_broad := fun _ _ => trivial
  strict_witness :=
    ⟨ThoughtBowlMechanicsRefined.unreachableBowlBigDamping,
     trivial,
     ThoughtBowlMechanicsRefined.unreachable_bowl_big_damping_is_unreachable⟩

/-- The unreachable-bowl witness factors through the strict refinement
    abstraction. -/
theorem unreachable_bowls_exist_via_refinement :
    ∃ b : EchoChamberAsTaoBowl.TaoBowl,
      True ∧ ¬ ThoughtBowlMechanicsRefined.IsReachable b :=
  taoBowlReachabilityStrictRefinement.gap

/-- Reachability is not equivalent to mere bowl inhabitation. -/
theorem all_bowls_not_equivalent_to_reachable_bowls :
    ¬ (∀ b : EchoChamberAsTaoBowl.TaoBowl,
        True ↔ ThoughtBowlMechanicsRefined.IsReachable b) :=
  taoBowlReachabilityStrictRefinement.not_equivalent

/-! ## Instance 3: richer phenomena vs representable phenomena -/

/-- Pattern D for affect completeness: all richer phenomena form the
    broad carrier, while single-cell grid representability is a
    strict fragment. -/
def affectRepresentabilityStrictRefinement :
    StrictPredicateRefinement AffectMatrixCompleteness.EmotionPhenomenon where
  broad := fun _ => True
  narrow := AffectMatrixCompleteness.IsRepresentable
  narrow_implies_broad := fun _ _ => trivial
  strict_witness :=
    let h := AffectMatrixCompleteness.phenomena_outside_grid_exist
    h.elim (fun p hp => ⟨p, trivial, hp⟩)

/-- The existing outside-grid theorem factors through the strict
    refinement abstraction. -/
theorem phenomena_outside_grid_exist_via_refinement :
    ∃ p : AffectMatrixCompleteness.EmotionPhenomenon,
      True ∧ ¬ AffectMatrixCompleteness.IsRepresentable p :=
  affectRepresentabilityStrictRefinement.gap

/-- Richer phenomena and single-cell representability are not
    equivalent predicates. -/
theorem all_phenomena_not_equivalent_to_representable_phenomena :
    ¬ (∀ p : AffectMatrixCompleteness.EmotionPhenomenon,
        True ↔ AffectMatrixCompleteness.IsRepresentable p) :=
  affectRepresentabilityStrictRefinement.not_equivalent

/-! ## Headline witness -/

/-- Bundles the three strict-refinement instances and their factored
    gap theorems. -/
theorem strict_refinement_lattice_pattern_witness :
    (∃ s : PolarizationState,
      BuleyErgodicClosure.forwardStep s = s ∧
      ¬ BuleyErgodicClosure.IsBulkNovikovClosed s) ∧
    (¬ (∀ s : PolarizationState,
        BuleyErgodicClosure.forwardStep s = s ↔
        BuleyErgodicClosure.IsBulkNovikovClosed s)) ∧
    (∃ b : EchoChamberAsTaoBowl.TaoBowl,
      True ∧ ¬ ThoughtBowlMechanicsRefined.IsReachable b) ∧
    (¬ (∀ b : EchoChamberAsTaoBowl.TaoBowl,
        True ↔ ThoughtBowlMechanicsRefined.IsReachable b)) ∧
    (∃ p : AffectMatrixCompleteness.EmotionPhenomenon,
      True ∧ ¬ AffectMatrixCompleteness.IsRepresentable p) ∧
    (¬ (∀ p : AffectMatrixCompleteness.EmotionPhenomenon,
        True ↔ AffectMatrixCompleteness.IsRepresentable p)) :=
  ⟨skyrms_admits_more_fixed_points_than_buley_via_refinement,
   skyrms_forward_fixed_not_equivalent_to_buley_closed,
   unreachable_bowls_exist_via_refinement,
   all_bowls_not_equivalent_to_reachable_bowls,
   phenomena_outside_grid_exist_via_refinement,
   all_phenomena_not_equivalent_to_representable_phenomena⟩

/-! ## Honesty note

What this module proves:

  * `StrictPredicateRefinement` captures the exact theorem shape
    "narrow implies broad, and broad has at least one non-narrow
    witness."
  * Three existing gaps factor through it: Skyrms vs Buley, reachable
    bowls vs all bowls, and representable affect phenomena vs richer
    phenomena.
  * Each gap also rules out predicate equivalence on its carrier type.

What this module does not prove:

  * It does not build injections between two different carrier types.
    The honest shared shape in the current code is predicate refinement
    on one carrier, not an arbitrary `Small -> Big` embedding.
  * It does not add new domain content. The strictness witnesses are
    imported from the existing modules and repackaged through the
    abstraction.
  * It does not rank the refinements by measure, cardinality, or
    probability. Strictness here is existential: one broad witness
    outside narrow is enough.

## Next exploration

`Gnosis/PatternAtlas.lean` - bundle Patterns A-D (`Retract`,
`InvariantHomomorphism`, `axisCells`, `StrictPredicateRefinement`) into
one atlas theorem that records which Gnosis modules instantiate which
structural shape, without forcing unrelated domains into a single
over-general abstraction.
-/

end StrictRefinementLatticePattern
