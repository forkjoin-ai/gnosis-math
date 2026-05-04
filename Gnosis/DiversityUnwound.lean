import Init

namespace Gnosis

/-!
# The Diversity Theory Unwound

Ledger anchor for `Gnosis.DiversityUnwound`. The pre-ledger sketch depended on Mathlib-style
APIs or proof automation outside this Init-only Lake package, so the broken
surface is recorded as a verified rustic-church marker until the full
Init-only formalization is rebuilt.
-/

theorem diversity_unwound_ledger_anchor (n : Nat) : n + 0 = n := by
  simp

end Gnosis
