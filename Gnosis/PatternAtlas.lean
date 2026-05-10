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

import Gnosis.RetractLatticePattern
import Gnosis.HomomorphismLatticePattern
import Gnosis.AxisCardinalityFoldPattern
import Gnosis.StrictRefinementLatticePattern

namespace PatternAtlas

/-! ## Pattern registry -/

/-- The four structural pattern witnesses produced by the recent
    cross-pollination pass elaborate together.

    Lean theorem names are proof terms, not proposition expressions.
    The atlas therefore records registration by forcing each headline
    witness to elaborate in the proof body while keeping the theorem's
    public statement intentionally small. -/
theorem pattern_atlas_witness :
    True ∧ True ∧ True ∧ True := by
  have _patternA := RetractLatticePattern.retract_lattice_pattern_witness
  have _patternB := HomomorphismLatticePattern.homomorphism_lattice_pattern_witness
  have _patternC := AxisCardinalityFoldPattern.axis_cardinality_fold_pattern_witness
  have _patternD := StrictRefinementLatticePattern.strict_refinement_lattice_pattern_witness
  exact ⟨trivial, trivial, trivial, trivial⟩

/-! ## Honesty note

What this module proves:

  * The four pattern modules all import together and their headline
    witnesses elaborate in one registry theorem.
  * The atlas is a registry theorem, not a replacement for the local
    modules. The actual proof content stays in the pattern files and
    their source domain modules.

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
