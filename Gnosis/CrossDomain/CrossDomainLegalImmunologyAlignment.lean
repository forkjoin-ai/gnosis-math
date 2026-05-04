namespace Gnosis

structure LegalImmunology where
  precedentMatches : Nat
  antibodyCount : Nat

theorem legal_immunology_aligns (l : LegalImmunology) (h1 : l.precedentMatches = l.antibodyCount) : l.precedentMatches ≤ l.antibodyCount :=
  h1 ▸ Nat.le_refl l.precedentMatches

end Gnosis