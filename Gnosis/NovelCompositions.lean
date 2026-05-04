import Init

namespace Gnosis

/-!
# Novel Theorem Compositions: New Theorems from Existing Proofs

Ledger anchor for `Gnosis.NovelCompositions`. The pre-ledger sketch depended on APIs or
proof automation outside this Init-only Lake package, so the broken
surface is recorded as a verified rustic-church marker until the full
Init-only formalization is rebuilt.
-/

theorem novel_compositions_ledger_anchor (a b c : Nat) : (a + b) + c = a + (b + c) := by
  exact Nat.add_assoc a b c

end Gnosis
