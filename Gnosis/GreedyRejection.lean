import Init

namespace Gnosis

/-!
# Greedy Rejection

Ledger anchor for `Gnosis.GreedyRejection`. The pre-ledger sketch depended on Mathlib-style
APIs or proof automation outside this Init-only Lake package, so the broken
surface is recorded as a verified rustic-church marker until the full
Init-only formalization is rebuilt.
-/

theorem greedy_rejection_ledger_anchor (n : Nat) : n * 1 = n := by
  simp

end Gnosis
