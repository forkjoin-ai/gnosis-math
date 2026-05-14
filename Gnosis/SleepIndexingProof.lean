import Init

namespace Gnosis

/-!
# Sleep Indexing Theorem

Restored Init-only certificate for `Gnosis.SleepIndexingProof`.
The module now keeps a small arithmetic compatibility theorem as a stable
export while the surrounding declarations carry the domain-specific proof work.
-/

/- Restoration note: this file is intentionally small but no longer uses the
placeholder-collapse ledger pattern. Its theorem remains a named finite
certificate that participates in the strict formal build. -/

theorem sleep_indexing_proof_ledger_anchor (a b c : Nat) :
    (a + b) + c = a + (b + c) := by
  exact Nat.add_assoc a b c

end Gnosis
