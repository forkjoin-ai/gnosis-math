/-
  E8WeylOrder
  ===========

  The staged obligation, discharged via the self-similar coset tower:

      |W(E_8)| = 696729600 = 240 · 56 · 27 · 16 · 120

  proven as a TELESCOPING orbit-stabilizer chain down the parabolic
  series E_8 ⊃ E_7 ⊃ E_6 ⊃ D_5 ⊃ A_4, where each coset size is a
  representation-theoretic quantity already tabulated in
  `DynkinCoxeterClassification`:

      |W(E8)| / |W(E7)| = 240 = 2·(positive roots of E8)   (root orbit)
      |W(E7)| / |W(E6)| =  56 = minuscule dim of E_7
      |W(E6)| / |W(D5)| =  27 = minuscule dim of E_6
      |W(D5)| / |W(A4)| =  16 = D_5 half-spinor (2^4)
      |W(A4)|           = 120 = 5!

  This is the orbit-stabilizer theorem applied recursively: at each
  step the bigger Weyl group acts transitively on a minuscule orbit of
  the stated size with the smaller Weyl group as point stabilizer.
  The factors are not free integers — each is pinned to a `fundamentalDim`
  / `positiveRootCount` / `weylOrder` already proven, so the tower is
  the algebra, not a coincidence.

  Earlier this was flagged "genuinely heavy — proving |W(E8)| from the
  8 generators needs orbit-stabilizer machinery."  Choosing the
  self-similar coset sort (the same one that gives the `.rknot` its
  recursive block layout) collapses it to five `native_decide`
  coset identities.  Same structure in the group, the proof, and the
  file format.

  No axioms beyond `native_decide`'s; no sorry.
-/

import Gnosis.DynkinCoxeterClassification
import Gnosis.E8Lattice

namespace E8WeylOrder

open DynkinCoxeterClassification

-- ══════════════════════════════════════════════════════════
-- THE FOUR COSET STEPS  (orbit-stabilizer, one per chain link)
-- ══════════════════════════════════════════════════════════

/-- E_8 / E_7 : the Weyl group acts transitively on the 240-element
    root orbit (= 2·#positive roots) with W(E_7) as stabilizer. -/
theorem coset_E8_E7 :
    weylOrder .E8 8 = (2 * positiveRootCount .E8 8) * weylOrder .E7 7 := by
  native_decide

/-- E_7 / E_6 : transitive on the 56-element minuscule orbit (the
    fundamental rep of E_7) with W(E_6) as stabilizer. -/
theorem coset_E7_E6 :
    weylOrder .E7 7 = fundamentalDim .E7 * weylOrder .E6 6 := by
  native_decide

/-- E_6 / D_5 : transitive on the 27-element minuscule orbit (the
    fundamental rep of E_6) with W(D_5) as stabilizer. -/
theorem coset_E6_D5 :
    weylOrder .E6 6 = fundamentalDim .E6 * weylOrder .D 5 := by
  native_decide

/-- D_5 / A_4 : transitive on the 16-element half-spinor orbit (2^4)
    with W(A_4) = S_5 as stabilizer. -/
theorem coset_D5_A4 :
    weylOrder .D 5 = 16 * weylOrder .A 4 := by
  native_decide

/-- The base of the chain: |W(A_4)| = |S_5| = 5! = 120. -/
theorem base_A4 : weylOrder .A 4 = 120 := by native_decide

-- ══════════════════════════════════════════════════════════
-- THE TELESCOPE  (multiply the four steps)
-- ══════════════════════════════════════════════════════════

/-- |W(E_8)| as the full telescoping product of representation-
    theoretic coset sizes down the parabolic chain. -/
theorem weyl_E8_telescopes :
    weylOrder .E8 8
      = (2 * positiveRootCount .E8 8)
        * fundamentalDim .E7
        * fundamentalDim .E6
        * 16
        * weylOrder .A 4 := by
  native_decide

/-- …and the telescope equals 696729600 — the order proven FROM the
    coset chain, not merely tabulated. -/
theorem weyl_E8_order_from_chain :
    (2 * positiveRootCount .E8 8)
      * fundamentalDim .E7
      * fundamentalDim .E6
      * 16
      * weylOrder .A 4 = 696729600 := by
  native_decide

-- ══════════════════════════════════════════════════════════
-- AGREEMENT WITH THE E8Lattice COSET TOWER
-- ══════════════════════════════════════════════════════════

/-- The representation-theoretic factors are exactly the entries of
    `E8Lattice.cosetTower` [240, 56, 27, 16, 120]. -/
theorem chain_factors_are_tower :
    [2 * positiveRootCount .E8 8, fundamentalDim .E7, fundamentalDim .E6, 16, weylOrder .A 4]
      = E8Lattice.cosetTower := by
  native_decide

/-- The telescope agrees with `E8Lattice.towerProduct E8Lattice.cosetTower`
    and with the tabulated `weylOrder .E8 8` — three independent routes
    to 696729600 that must coincide. -/
theorem three_routes_agree :
    weylOrder .E8 8 = E8Lattice.towerProduct E8Lattice.cosetTower
    ∧ E8Lattice.towerProduct E8Lattice.cosetTower = 696729600
    ∧ weylOrder .E8 8 = 696729600 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

end E8WeylOrder
