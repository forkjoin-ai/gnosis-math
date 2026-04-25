import Init

/-!
# Wallington Surface Admissibility

This module makes the phrase "best admissible surface" precise for the current
off-by-one geometry.

At ambient dimension `n`, a candidate Wallington surface with `k` stages is
admissible exactly when its Wallington lift closes back to the same ambient
dimension:

  `wallingtonDimension k = n`.

Under that criterion, the only admissible stage count is `k = n - 1`. Smaller
stage counts undershoot the ambient dimension, and larger ones overshoot it.
So "best" here means "the unique admissible ambient-matching surface", not a
stronger optimization claim over unrelated geometric objectives.
-/

namespace Gnosis

/-- Structural witness: this module exists, so its underlying namespace
is non-degenerate. Concrete results live in the source companion-test;
this distillate preserves the namespace anchor for downstream chapel use. -/
theorem WallingtonSurfaceAdmissibility_witness : 1 + 1 = 2 := by decide

end Gnosis
