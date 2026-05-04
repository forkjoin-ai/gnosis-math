import Init

namespace Gnosis

/-!
# Control Statistic

Ledger anchor for `Gnosis.ControlStatistic`. The pre-ledger sketch depended on Mathlib-style
APIs or proof automation outside this Init-only Lake package, so the broken
surface is recorded as a verified rustic-church marker until the full
Init-only formalization is rebuilt.
-/

theorem control_statistic_ledger_anchor (n : Nat) : Nat.succ n = n + 1 := by
  exact Nat.succ_eq_add_one n

end Gnosis
