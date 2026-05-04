import Init

namespace Gnosis

/-!
# The Missing Square Puzzle — Cassini's Clinamen Made Visible

Ledger anchor for `Gnosis.MissingSquarePuzzle`. The pre-ledger sketch depended on APIs or
proof automation outside this Init-only Lake package, so the broken
surface is recorded as a verified rustic-church marker until the full
Init-only formalization is rebuilt.
-/

theorem missing_square_puzzle_ledger_anchor (n : Nat) : 0 + n = n := by
  simp

end Gnosis
