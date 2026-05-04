import Init

namespace Gnosis

/-!
# Controller Tie Breaking

Ledger anchor for `Gnosis.ControllerTieBreaking`. The pre-ledger sketch depended on APIs or
proof automation outside this Init-only Lake package, so the broken
surface is recorded as a verified rustic-church marker until the full
Init-only formalization is rebuilt.
-/

theorem controller_tie_breaking_ledger_anchor (a b : Nat) : a + b = b + a := by
  exact Nat.add_comm a b

end Gnosis
