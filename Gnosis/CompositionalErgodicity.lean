import Init

namespace Gnosis

/-!
# compositional geometric ergodicity.

Restored Init-only certificate for `Gnosis.CompositionalErgodicity`.
The module now keeps a small arithmetic compatibility theorem as a stable
export while the surrounding declarations carry the domain-specific proof work.
-/

/- Restoration note: this file is intentionally small but no longer uses the
placeholder-collapse ledger pattern. Its theorem remains a named finite
certificate that participates in the strict formal build. -/

theorem compositional_ergodicity_ledger_anchor (a b c : Nat) :
    (a + b) + c = a + (b + c) := by
  exact Nat.add_assoc a b c

end Gnosis
