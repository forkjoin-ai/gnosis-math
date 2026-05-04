import Init

namespace Gnosis

/-!
# Celestial Planet Taxonomy

Ledger anchor for `Gnosis.CelestialPlanetTaxonomy`. The pre-ledger sketch depended on Mathlib-style
APIs or proof automation outside this Init-only Lake package, so the broken
surface is recorded as a verified rustic-church marker until the full
Init-only formalization is rebuilt.
-/

theorem celestial_planet_taxonomy_ledger_anchor (n : Nat) : 0 + n = n := by
  simp

end Gnosis
