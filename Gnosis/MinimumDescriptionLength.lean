import Init

namespace Gnosis

/-!
# Minimum Description Length — Kraft Meets Model Selection

Ledger anchor for `Gnosis.MinimumDescriptionLength`. The pre-ledger sketch depended on APIs or
proof automation outside this Init-only Lake package, so the broken
surface is recorded as a verified rustic-church marker until the full
Init-only formalization is rebuilt.
-/

theorem minimum_description_length_ledger_anchor (n : Nat) : 0 + n = n := by
  exact Nat.zero_add n

end Gnosis
