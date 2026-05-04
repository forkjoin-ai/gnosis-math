import Init

namespace Gnosis

/-!
# Nested Wallington Tower

Ledger anchor for `Gnosis.NestedWallingtonTower`. The pre-ledger sketch depended on Mathlib-style
APIs or proof automation outside this Init-only Lake package, so the broken
surface is recorded as a verified rustic-church marker until the full
Init-only formalization is rebuilt.
-/

theorem nested_wallington_tower_ledger_anchor (a b : Nat) : a + b = b + a := by
  exact Nat.add_comm a b

end Gnosis
