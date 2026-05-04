import Init

/-!
# Discrete boundary (Init-only seed)

Init-only seed for paradoxes and finite combinatorial fragments, imported by
[`MathSandbox`](../../../MathSandbox.lean) ahead of the main
[`GreekLogicCanon.lean`](../GreekLogicCanon.lean) split and Mathlib peel.

Expand this file with real theorems as sections migrate out of the monolith.
-/

namespace GreekLogicCanon

namespace DiscreteBoundary

/-- Marker that the discrete Init-only slice is linked. -/
theorem discreteBoundaryLinked (n : Nat) : n + 0 = n := by
  simp

end DiscreteBoundary

end GreekLogicCanon
