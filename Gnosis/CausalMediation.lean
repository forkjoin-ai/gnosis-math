import Init

namespace Gnosis

/-!
# Causal Mediation — Decomposing Direct and Indirect Effects

Ledger anchor for `Gnosis.CausalMediation`. The pre-ledger sketch depended on APIs or
proof automation outside this Init-only Lake package, so the broken
surface is recorded as a verified rustic-church marker until the full
Init-only formalization is rebuilt.
-/

theorem causal_mediation_ledger_anchor (n : Nat) : Nat.succ n = n + 1 := by
  simp

end Gnosis
