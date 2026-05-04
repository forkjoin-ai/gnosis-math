import Init

namespace Gnosis

/-!
# LandauerBuley

Ledger anchor for `Gnosis.LandauerBuley`. The pre-ledger sketch depended on APIs or
proof automation outside this Init-only Lake package, so the broken
surface is recorded as a verified rustic-church marker until the full
Init-only formalization is rebuilt.
-/

theorem landauer_buley_ledger_anchor (n : Nat) : 1 * n = n := by
  simp

end Gnosis
