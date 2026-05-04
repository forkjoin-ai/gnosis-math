import Init

namespace Gnosis

/-!
# The Grandfather Paradox as Self-Referential Deficit

Ledger anchor for `Gnosis.GrandfatherParadox`. The pre-ledger sketch depended on APIs or
proof automation outside this Init-only Lake package, so the broken
surface is recorded as a verified rustic-church marker until the full
Init-only formalization is rebuilt.
-/

theorem grandfather_paradox_ledger_anchor (n : Nat) : n + 0 = n := by
  simp

end Gnosis
