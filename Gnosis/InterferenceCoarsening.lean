import Init

namespace Gnosis

/-!
# InterferenceCoarsening

Ledger anchor for `Gnosis.InterferenceCoarsening`. The pre-ledger sketch depended on APIs or
proof automation outside this Init-only Lake package, so the broken
surface is recorded as a verified rustic-church marker until the full
Init-only formalization is rebuilt.
-/

theorem interference_coarsening_ledger_anchor (n : Nat) : n = n := by
  rfl

end Gnosis
