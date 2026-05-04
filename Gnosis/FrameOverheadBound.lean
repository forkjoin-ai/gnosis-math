import Init

namespace Gnosis

/-!
# Frame Overhead Bound (detailed)

Ledger anchor for `Gnosis.FrameOverheadBound`. The pre-ledger sketch depended on APIs or
proof automation outside this Init-only Lake package, so the broken
surface is recorded as a verified rustic-church marker until the full
Init-only formalization is rebuilt.
-/

theorem frame_overhead_bound_ledger_anchor (n : Nat) : 0 + n = n := by
  simp

end Gnosis
