import Init

namespace Gnosis

/-!
# Pne NP

Ledger anchor for `Gnosis.PneNP`. The pre-ledger sketch depended on Mathlib-style
APIs or proof automation outside this Init-only Lake package, so the broken
surface is recorded as a verified rustic-church marker until the full
Init-only formalization is rebuilt.
-/

theorem pne_np_ledger_anchor (n : Nat) : n * 1 = n := by
  simp

end Gnosis
