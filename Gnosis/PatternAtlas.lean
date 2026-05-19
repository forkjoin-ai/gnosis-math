import Gnosis.RetractLatticePattern
import Gnosis.HomomorphismLatticePattern
import Gnosis.AxisCardinalityFoldPattern
import Gnosis.StrictRefinementLatticePattern

/-
  PatternAtlas.lean
  =================

  A small index theorem for the four cross-pollination patterns
  factored out of today's Gnosis modules.

  The atlas deliberately does not merge the patterns into a single
  over-general structure. Each abstraction has a distinct proof shape:

  * Pattern A: `Retract` - forget-and-recover on a reachable subset.
  * Pattern B: `InvariantHomomorphism` - lift while preserving an
    invariant.
  * Pattern C: `axisCells` - coordinate-count growth as a product fold.
  * Pattern D: `StrictPredicateRefinement` - narrow implies broad, with
    a broad witness outside narrow.

  Zero `sorry`, zero new `axiom`.
-/


namespace PatternAtlas

/-! ## Pattern registry -/

/-- The conjunction of the four pattern propositions. Each conjunct is
    the abbrev exported by its pattern module, so this proposition is
    pinned to whatever those modules actually claim. -/
abbrev PatternAtlasWitness : Prop :=
  RetractLatticePattern.RetractLatticeWitness ∧
  HomomorphismLatticePattern.HomomorphismLatticeWitness ∧
  AxisCardinalityFoldPattern.AxisCardinalityFoldWitness ∧
  StrictRefinementLatticePattern.StrictRefinementLatticeWitness

/-- The four structural pattern witnesses produced by the recent
    cross-pollination pass, bundled. Each component is the headline
    witness of its pattern module, accessible by `.1`, `.2.1`, `.2.2.1`,
    and `.2.2.2`. -/
theorem pattern_atlas_witness : PatternAtlasWitness :=
  ⟨RetractLatticePattern.retract_lattice_pattern_witness,
   HomomorphismLatticePattern.homomorphism_lattice_pattern_witness,
   AxisCardinalityFoldPattern.axis_cardinality_fold_pattern_witness,
   StrictRefinementLatticePattern.strict_refinement_lattice_pattern_witness⟩

/-! ## Direct accessors

  Convenience names that pull each pattern witness out of the bundle. -/

theorem patternA_witness : RetractLatticePattern.RetractLatticeWitness :=
  pattern_atlas_witness.1

theorem patternB_witness : HomomorphismLatticePattern.HomomorphismLatticeWitness :=
  pattern_atlas_witness.2.1

theorem patternC_witness : AxisCardinalityFoldPattern.AxisCardinalityFoldWitness :=
  pattern_atlas_witness.2.2.1

theorem patternD_witness : StrictRefinementLatticePattern.StrictRefinementLatticeWitness :=
  pattern_atlas_witness.2.2.2

/-! ## Honesty note

What this module proves:

  * `PatternAtlasWitness` is the proposition `A ∧ B ∧ C ∧ D` where each
    conjunct is the named `abbrev` exported by its pattern module.
  * `pattern_atlas_witness` is a real proof of that conjunction; each
    component is the corresponding module's headline theorem.
  * Four `patternX_witness` accessors expose the components by name so
    downstream modules can extract them without index arithmetic.

What this module does not prove:

  * It does not claim the four patterns are one pattern. They are four
    different abstractions with different data and proof obligations.
  * It does not add new instances. It records the current atlas so a
    later module can extend it deliberately.

## Next exploration

`Gnosis/PatternAtlasExtensions.lean` - add new rows only when a fresh
domain module supplies a real theorem-level instance of one of the four
pattern shapes, rather than by analogy alone.
-/

end PatternAtlas
