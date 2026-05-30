/-
  G2OctonionAutomorphism
  ======================

  The G₂ rung of the exceptional ascent, tied to the octonions.

  THE MEANING (cited group/algebra facts, NOT formalized here)
  ------------------------------------------------------------
  G₂ = Aut(𝕆), the automorphism group of the octonions; equivalently its Lie
  algebra g₂ = Der(𝕆), the derivation algebra of the octonions. This is the
  classical Cartan fact (É. Cartan, 1914): the smallest exceptional simple Lie
  algebra is exactly the derivations of the octonion algebra, and it has
  dimension 14. G₂ acts on the 7-dimensional space of imaginary (purely
  imaginary) octonions — the trace-zero part 𝕆₀, of dimension 8 − 1 = 7 — and
  the 7-dimensional irreducible representation is the smallest non-trivial rep
  of G₂ (`fundamentalDim .G2 = 7` in the SSOT).

  WHAT IS PROVED HERE (dimension arithmetic + ordering)
  -----------------------------------------------------
  Everything below is finite/decidable and closes by kernel `decide` / `rfl`.
  The single source of truth for the dimension is
  `DynkinCoxeterClassification` (the Cartan–Killing tabulation of rank, Coxeter
  number, and positive-root count) re-expressed through
  `OctavianCubicMagicSquare.lieAlgebraDim t n = 2·(#positive roots) + n`.

    * dim g₂ = 14 = 2·(positiveRootCount .G2 2) + 2 = lieAlgebraDim .G2 2.
      G₂ has rank 2 and 6 positive roots, so 2·6 + 2 = 14.
    * The exceptional ascent STARTS at G₂: the strict dimension chain
      14 (G₂) < 52 (F₄) < 78 (E₆) < 133 (E₇) < 248 (E₈), each equal to the
      `lieAlgebraDim` of its type.
    * 7 = octonionDim − 1 (G₂ acts on the 7-dim imaginary octonions).
    * 14 = 7 + 7 as arithmetic. The clean 7+7=14 in the octonion construction is
      the half-integer quad structure `OctavianLoop.quads` (7 Coxeter triples,
      each contributing a quad `{0}∪triple` plus its complement). See CORRECTION.

  CORRECTION (a claim verified-and-dropped)
  -----------------------------------------
  An earlier framing wanted "14 = 7 + 7 = the G₂ root structure". This is FALSE
  and is dropped: G₂ has 12 roots (6 positive, 6 negative), not 14, so 14 is the
  algebra dimension (roots + Cartan = 12 + 2), never a "7+7 root count". The
  honest 7+7=14 lives in the octonion half-unit quad structure
  (`OctavianLoop.quad_count : quads.length = 14`), where the two 7's are the
  Coxeter triples and their complements among the 7 imaginary indices. The
  7-dimensional object G₂ genuinely acts on is the imaginary octonions
  (`octonionDim − 1`), proved below.

  Init + `DynkinCoxeterClassification` + `OctavianCubicMagicSquare`. No Mathlib.
  Zero `sorry`, zero new `axiom`, no `Classical`, no `native_decide`.
-/

import Gnosis.DynkinCoxeterClassification
import Gnosis.OctavianCubicMagicSquare

namespace Gnosis.G2OctonionAutomorphism

open DynkinCoxeterClassification (DynkinType rank positiveRootCount fundamentalDim)
open Gnosis.OctavianCubicMagicSquare (lieAlgebraDim octonionDim)

-- ══════════════════════════════════════════════════════════
-- dim g₂ = 14  (from the SSOT)
-- ══════════════════════════════════════════════════════════

/-- The dimension of G₂. The meaning: G₂ = Aut(𝕆), and g₂ = Der(𝕆), the
    derivation algebra of the octonions, which is 14-dimensional. The number
    14 is what is proved; the identification with Der(𝕆) is the cited Cartan
    fact. -/
def g2Dim : Nat := 14

/-- G₂ has rank 2 and 6 positive roots (the SSOT). -/
theorem g2_rank_two : rank .G2 2 = 2 := by decide
theorem g2_positive_roots_six : positiveRootCount .G2 2 = 6 := by decide

/-- dim g₂ = 2·(#positive roots) + rank = 2·6 + 2 = 14, via the magic-square
    `lieAlgebraDim`. -/
theorem g2_dim_eq_lieAlgebraDim : g2Dim = lieAlgebraDim .G2 2 := by decide

/-- dim g₂ = 14, written out as the root/rank arithmetic. -/
theorem g2_dim_fourteen :
    g2Dim = 2 * positiveRootCount .G2 2 + 2 := by decide

/-- dim g₂ = 14 (numeral). -/
theorem g2_dim_is_14 : lieAlgebraDim .G2 2 = 14 := by decide

-- ══════════════════════════════════════════════════════════
-- THE EXCEPTIONAL ASCENT STARTS AT G₂
-- ══════════════════════════════════════════════════════════
-- 14 (G₂) < 52 (F₄) < 78 (E₆) < 133 (E₇) < 248 (E₈)

/-- Each exceptional dimension equals the `lieAlgebraDim` of its type. -/
theorem exceptional_dims :
      lieAlgebraDim .G2 2 = 14
    ∧ lieAlgebraDim .F4 4 = 52
    ∧ lieAlgebraDim .E6 6 = 78
    ∧ lieAlgebraDim .E7 7 = 133
    ∧ lieAlgebraDim .E8 8 = 248 := by decide

/-- The strict ascending chain of exceptional dimensions, with G₂ at the
    start. -/
theorem exceptional_ascent_strict :
      lieAlgebraDim .G2 2 < lieAlgebraDim .F4 4
    ∧ lieAlgebraDim .F4 4 < lieAlgebraDim .E6 6
    ∧ lieAlgebraDim .E6 6 < lieAlgebraDim .E7 7
    ∧ lieAlgebraDim .E7 7 < lieAlgebraDim .E8 8 := by decide

/-- G₂ is the smallest exceptional Lie algebra: its dimension is strictly less
    than every other exceptional dimension. -/
theorem g2_is_smallest_exceptional :
      lieAlgebraDim .G2 2 < lieAlgebraDim .F4 4
    ∧ lieAlgebraDim .G2 2 < lieAlgebraDim .E6 6
    ∧ lieAlgebraDim .G2 2 < lieAlgebraDim .E7 7
    ∧ lieAlgebraDim .G2 2 < lieAlgebraDim .E8 8 := by decide

-- ══════════════════════════════════════════════════════════
-- G₂ ACTS ON THE 7 IMAGINARY OCTONIONS
-- ══════════════════════════════════════════════════════════

/-- The octonions are 8-dimensional (the "Octavian", from the SSOT). -/
theorem octonion_dim_eight : octonionDim = 8 := by decide

/-- The imaginary octonions form a 7-dimensional space: 7 = octonionDim − 1
    (the trace-zero / purely-imaginary part 𝕆₀ that G₂ acts on irreducibly). -/
theorem imaginary_octonion_dim_seven : octonionDim - 1 = 7 := by decide

/-- G₂'s smallest non-trivial representation is 7-dimensional — exactly the
    imaginary octonions (`fundamentalDim .G2 = 7` in the SSOT). -/
theorem g2_fundamental_is_imaginary_octonions :
    fundamentalDim .G2 = octonionDim - 1 := by decide

-- ══════════════════════════════════════════════════════════
-- 14 = 7 + 7  (arithmetic; the octonion quad structure)
-- ══════════════════════════════════════════════════════════
-- NOTE: this 7+7 is NOT the G₂ root count (G₂ has 12 roots). It is the
-- half-integer octavian quad structure: 7 Coxeter triples + 7 complements
-- = 14 quads (`OctavianLoop.quad_count : quads.length = 14`), and the two 7's
-- live among the 7 imaginary octonion indices {1,…,7}.

/-- dim g₂ = 14 = 7 + 7, with each 7 = octonionDim − 1 = the imaginary-octonion
    dimension. Pure arithmetic tie; see the file CORRECTION for why this is the
    quad structure and NOT a root decomposition. -/
theorem g2_dim_seven_plus_seven :
    lieAlgebraDim .G2 2 = (octonionDim - 1) + (octonionDim - 1) := by decide

-- ══════════════════════════════════════════════════════════
-- SUMMARY
-- ══════════════════════════════════════════════════════════

/-- The G₂ octonion-automorphism rung, bundled:
      * dim g₂ = 14 = lieAlgebraDim .G2 2 = 2·6 + 2
      * G₂ starts the strict exceptional ascent 14 < 52 < 78 < 133 < 248
      * G₂ acts on the 7 = octonionDim − 1 imaginary octonions
      * 14 = 7 + 7 (octonion quad arithmetic, not a root count). -/
theorem g2_octonion_automorphism_rung :
      lieAlgebraDim .G2 2 = 14
    ∧ lieAlgebraDim .G2 2 = 2 * positiveRootCount .G2 2 + rank .G2 2
    ∧ lieAlgebraDim .G2 2 < lieAlgebraDim .F4 4
    ∧ lieAlgebraDim .F4 4 < lieAlgebraDim .E6 6
    ∧ lieAlgebraDim .E6 6 < lieAlgebraDim .E7 7
    ∧ lieAlgebraDim .E7 7 < lieAlgebraDim .E8 8
    ∧ octonionDim - 1 = 7
    ∧ fundamentalDim .G2 = octonionDim - 1
    ∧ lieAlgebraDim .G2 2 = (octonionDim - 1) + (octonionDim - 1) := by decide

end Gnosis.G2OctonionAutomorphism
