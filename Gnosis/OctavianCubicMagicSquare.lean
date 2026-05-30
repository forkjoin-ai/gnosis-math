/-
  OctavianCubicMagicSquare
  ========================

  The "Cubic" that `OctavianMoufangCubic` names, completed at the dimension /
  arithmetic level: the octonion cubic Jordan algebra and the Freudenthal–Tits
  magic-square nesting that carries octonions → 27 → E₆ → E₇ → E₈.

  The thread of the toy's name:
    * OCTAVIAN — the octonions, dimension 8 (the 240 unit octavians = E₈ roots).
    * MOUFANG  — the degree-3 (cubic) Moufang identities of the octavian loop
                 (`OctavianMoufangCubic`).
    * CUBIC    — the degree-3 norm form ("determinant") of the 3×3 Hermitian
                 octonion matrices, the 27-dimensional exceptional Jordan
                 (Albert) algebra J₃(𝕆).

  The Albert algebra J₃(𝕆) is 27-dimensional: 3 real diagonal entries + 3
  octonion off-diagonal entries = 3 + 3·8 = 27. Its cubic norm form is fixed by
  E₆; building the structure/conformal/Tits-Kantor-Koecher towers on it gives
  the exceptional Lie algebras, whose dimensions nest along the octonion row of
  the magic square:

      dim E₆ = dim F₄ + (27 − 1)        78 = 52 + 26   (F₄ + traceless Albert)
      dim E₇ = dim E₆ + (2·27 + 1)      133 = 78 + 55  (Freudenthal triple)
      dim E₈ = dim E₇ + (2·56 + 3)      248 = 133 + 115

  and `27 = |E₆/D₅|`, `56 = |E₇/E₆|` are exactly the middle factors of the E₈
  Weyl coset tower `[240,56,27,16,120]` (`E8Lattice.cosetTower`). The 56 is the
  minuscule E₇ representation.

  Every dimension is derived from the single source of truth
  `DynkinCoxeterClassification` as `dim g = 2·(#positive roots) + rank`. All
  facts are finite/decidable; proved by kernel `decide`/`rfl`.

  DEFERRED (cited, not formalized — needs the actual algebra/group, i.e. Mathlib):
  the cubic norm form as a polynomial on J₃(𝕆), that its invariance group is
  E₆, the Tits–Kantor–Koecher / Freudenthal constructions of the Lie algebras
  themselves, and the full magic square. Only the dimension arithmetic and the
  coset-tower / SSOT ties are proved here.

  Init + `E8Lattice` + `DynkinCoxeterClassification`. Zero `sorry`, zero new `axiom`.
-/

import Gnosis.E8Lattice
import Gnosis.DynkinCoxeterClassification

namespace Gnosis.OctavianCubicMagicSquare

open DynkinCoxeterClassification

-- ══════════════════════════════════════════════════════════
-- THE ALBERT ALGEBRA  (the 27, the "Cubic")
-- ══════════════════════════════════════════════════════════

/-- Octonion dimension — the "Octavian". -/
def octonionDim : Nat := 8

/-- The exceptional Jordan (Albert) algebra J₃(𝕆): 3×3 Hermitian octonion
    matrices = 3 real diagonal entries + 3 octonion off-diagonal entries. -/
def albertDim : Nat := 3 + 3 * octonionDim

/-- The Jordan norm form (the "Cubic") and the Moufang identities are both
    degree 3. -/
def cubicDegree : Nat := 3

theorem albert_dim_27 : albertDim = 27 := by decide

/-- The 27 is `3 + 3·8` — three real diagonal slots and three octonion
    off-diagonal slots. -/
theorem albert_decomposes : albertDim = 3 + 3 * octonionDim := rfl

/-- The traceless Albert algebra (the F₄ module) has dimension 26 = 27 − 1. -/
theorem traceless_albert_26 : albertDim - 1 = 26 := by decide

/-- The norm form and the Moufang identities share degree 3 — the "Cubic". -/
theorem cubic_is_degree_three : cubicDegree = 3 := rfl

-- ══════════════════════════════════════════════════════════
-- EXCEPTIONAL LIE ALGEBRA DIMENSIONS  (from the SSOT)
-- ══════════════════════════════════════════════════════════

/-- Dimension of a simple Lie algebra: `2·(#positive roots) + rank`. The
    positive-root count comes from `DynkinCoxeterClassification`. -/
def lieAlgebraDim (t : DynkinType) (n : Nat) : Nat :=
  2 * positiveRootCount t n + n

theorem dim_F4 : lieAlgebraDim .F4 4 = 52 := by decide
theorem dim_E6 : lieAlgebraDim .E6 6 = 78 := by decide
theorem dim_E7 : lieAlgebraDim .E7 7 = 133 := by decide
theorem dim_E8 : lieAlgebraDim .E8 8 = 248 := by decide

-- ══════════════════════════════════════════════════════════
-- THE FREUDENTHAL–TITS MAGIC-SQUARE NESTING  (octonion row)
-- ══════════════════════════════════════════════════════════

/-- **E₆ = F₄ + traceless Albert.** `dim E₆ = dim F₄ + (27 − 1)`: 78 = 52 + 26.
    F₄ is the automorphism algebra of J₃(𝕆); E₆ adds the 26-dim traceless part
    the cubic norm sees. -/
theorem e6_from_f4_and_albert :
    lieAlgebraDim .E6 6 = lieAlgebraDim .F4 4 + (albertDim - 1) := by decide

/-- **E₇ = E₆ + Freudenthal triple.** `dim E₇ = dim E₆ + (2·27 + 1)`:
    133 = 78 + 55. The 56 = 27 + 27 + 1 + 1 Freudenthal structure sits over E₆. -/
theorem e7_from_e6_and_albert :
    lieAlgebraDim .E7 7 = lieAlgebraDim .E6 6 + (2 * albertDim + 1) := by decide

/-- **E₈ = E₇ + the 56-triple.** `dim E₈ = dim E₇ + (2·56 + 3)`: 248 = 133 + 115,
    where 56 is the minuscule E₇ module (`E8Lattice.cosetTower[1]`). -/
theorem e8_from_e7_and_56 :
    lieAlgebraDim .E8 8 = lieAlgebraDim .E7 7 + (2 * 56 + 3) := by decide

-- ══════════════════════════════════════════════════════════
-- TIES TO THE E₈ WELY COSET TOWER  (the 27 and 56 are tower factors)
-- ══════════════════════════════════════════════════════════

/-- **The Albert dimension 27 is the `|E₆/D₅|` factor of the E₈ coset tower.**
    `cosetTower = [240,56,27,16,120]`. -/
theorem albert_is_E6_D5_tower_factor :
    E8Lattice.cosetTower[2]? = some albertDim := by decide

/-- **The 56 in the E₈ → E₇ Freudenthal step is the `|E₇/E₆|` tower factor** —
    the minuscule E₇ representation. -/
theorem fiftysix_is_E7_E6_tower_factor :
    E8Lattice.cosetTower[1]? = some 56 := by decide

/-- **dim E₈ = 2·(#E₈ positive roots) + rank = 2·120 + 8 = 248** — and `2·120`
    counts the 240 E₈ roots (`E8Lattice.e8_root_count`), `+8` the Cartan, exactly
    `E8LeechMonsterTower.e8_dim_decomposes` (248 = 240 + 8). -/
theorem dimE8_is_roots_plus_rank :
    lieAlgebraDim .E8 8 = 2 * positiveRootCount .E8 8 + 8
      ∧ positiveRootCount .E8 8 = 120
      ∧ lieAlgebraDim .E8 8 = 240 + 8 := by
  refine ⟨rfl, by decide, by decide⟩

-- ══════════════════════════════════════════════════════════
-- MASTER CERTIFICATE
-- ══════════════════════════════════════════════════════════

/-- **OCTAVIAN–CUBIC–MAGIC-SQUARE.** The octonion (dim 8) cubic Jordan algebra
    J₃(𝕆) has dimension 27 = 3 + 3·8; its degree-3 norm form (the "Cubic", same
    degree as the octavian Moufang identities) seeds the Freudenthal–Tits
    octonion row, whose Lie-algebra dimensions nest
    `52 → 78 → 133 → 248` via the Albert algebra (27) and the minuscule 56; and
    27, 56 are exactly the E₆/D₅ and E₇/E₆ factors of the E₈ Weyl coset tower. -/
theorem octavian_cubic_magic_square :
    octonionDim = 8
    ∧ albertDim = 27
    ∧ cubicDegree = 3
    ∧ lieAlgebraDim .F4 4 = 52
    ∧ lieAlgebraDim .E6 6 = 78
    ∧ lieAlgebraDim .E7 7 = 133
    ∧ lieAlgebraDim .E8 8 = 248
    ∧ lieAlgebraDim .E6 6 = lieAlgebraDim .F4 4 + (albertDim - 1)
    ∧ lieAlgebraDim .E7 7 = lieAlgebraDim .E6 6 + (2 * albertDim + 1)
    ∧ lieAlgebraDim .E8 8 = lieAlgebraDim .E7 7 + (2 * 56 + 3)
    ∧ E8Lattice.cosetTower[2]? = some albertDim
    ∧ E8Lattice.cosetTower[1]? = some 56 := by
  refine ⟨rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Gnosis.OctavianCubicMagicSquare
