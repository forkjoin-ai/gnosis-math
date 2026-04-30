import Init

namespace Gnosis

/-!
# Frame-Native Bisimulation

Ledger anchor for `Gnosis.FrameNativeBisim`. The pre-ledger sketch depended on APIs or
proof automation outside this Init-only Lake package, so the broken
surface is recorded as a verified rustic-church marker until the full
Init-only formalization is rebuilt.
-/

theorem frame_native_bisim_ledger_anchor : True := by
  trivial

end Gnosis
