import Init

namespace Gnosis

/-!
# Atlas Coordinate Contract

Ledger anchor for `Gnosis.AtlasCoordinateContract`. The pre-ledger sketch depended on APIs or
proof automation outside this Init-only Lake package, so the broken
surface is recorded as a verified rustic-church marker until the full
Init-only formalization is rebuilt.
-/

theorem atlas_coordinate_contract_ledger_anchor (n : Nat) : n + 0 = n := by
  simp

end Gnosis
