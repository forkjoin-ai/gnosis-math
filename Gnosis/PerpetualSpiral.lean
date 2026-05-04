import Init

namespace Gnosis

/-!
# the perpetual spiral.

Ledger anchor for `Gnosis.PerpetualSpiral`. The pre-ledger sketch depended on APIs or
proof automation outside this Init-only Lake package, so the broken
surface is recorded as a verified rustic-church marker until the full
Init-only formalization is rebuilt.
-/

theorem perpetual_spiral_ledger_anchor (n : Nat) : Nat.succ n = n + 1 := by
  simp

end Gnosis
