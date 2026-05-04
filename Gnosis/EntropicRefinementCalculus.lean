import Init

namespace Gnosis

/-!
# EntropicRefinementCalculus

Ledger anchor for `Gnosis.EntropicRefinementCalculus`. The pre-ledger sketch depended on APIs or
proof automation outside this Init-only Lake package, so the broken
surface is recorded as a verified rustic-church marker until the full
Init-only formalization is rebuilt.
-/

theorem entropic_refinement_calculus_ledger_anchor (n : Nat) : n * 1 = n := by
  simp

end Gnosis
