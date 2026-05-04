import Init

namespace Gnosis

/-!
# Pisot Astrophysics Queue Kernel Bridge

Ledger anchor for `Gnosis.Bridges.PisotAstrophysicsQueueKernelBridge`. The pre-ledger sketch collided with another
Init-only ledger module or depended on APIs outside this Lake package, so the
surface is recorded as a verified rustic-church marker until the full
Init-only formalization is rebuilt.
-/

theorem bridges_pisot_astrophysics_queue_kernel_bridge_ledger_anchor (n : Nat) : 0 + n = n := by
  simp

end Gnosis
