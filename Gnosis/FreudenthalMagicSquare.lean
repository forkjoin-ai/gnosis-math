/-
  FreudenthalMagicSquare
  ======================

  The full 4×4 Freudenthal–Tits magic square of Lie-algebra dimensions, rows and
  columns indexed by the four normed division algebras

      ℝ (dim 1),  ℂ (dim 2),  ℍ (dim 4),  𝕆 (dim 8).

  The symmetric (Tits/Vinberg) magic square M(A,B):

            ℝ      ℂ      ℍ      𝕆
      ℝ    A₁=3   A₂=8   C₃=21  F₄=52
      ℂ    A₂=8  2A₂=16  A₅=35  E₆=78
      ℍ    C₃=21  A₅=35  D₆=66  E₇=133
      𝕆    F₄=52  E₆=78  E₇=133 E₈=248

  Every simple entry's dimension is derived from the single source of truth
  `DynkinCoxeterClassification` as `dim g = 2·(#positive roots) + rank`; the
  (ℂ,ℂ) entry is `su(3)⊕su(3)`, dimension `2·8 = 16`. The octonion row/column is
  the exceptional row `F₄,E₆,E₇,E₈` already tied to the E₈ coset tower in
  `OctavianCubicMagicSquare`.

  PROVED: the 10 distinct dimensions (each via `lieAlgebraDim` of its Dynkin
  type), the square's symmetry `M[i][j] = M[j][i]`, and the octonion row =
  exceptional row. DEFERRED (cited): the actual magic-square Lie-algebra
  constructions (Tits' unified bilinear form on `der(A) ⊕ (A₀⊗J₀) ⊕ der(J)`,
  the Vinberg symmetric version) — only the dimension arithmetic is formalized.

  Init + `DynkinCoxeterClassification`. Zero `sorry`, zero new `axiom`.
-/

import Gnosis.DynkinCoxeterClassification

namespace Gnosis.FreudenthalMagicSquare

open DynkinCoxeterClassification

/-- Dimension of a simple Lie algebra: `2·(#positive roots) + rank`. -/
def lieAlgebraDim (t : DynkinType) (n : Nat) : Nat :=
  2 * positiveRootCount t n + n

/-- Division-algebra dimensions indexing the rows/cols: ℝ,ℂ,ℍ,𝕆. -/
def divDims : List Nat := [1, 2, 4, 8]

/-- The symmetric Freudenthal–Tits magic square of Lie-algebra dimensions. -/
def magicTable : List (List Nat) :=
  [ [3,   8,   21,  52],
    [8,   16,  35,  78],
    [21,  35,  66,  133],
    [52,  78,  133, 248] ]

/-- Cell accessor with default 0. -/
def cell (i j : Nat) : Nat := (magicTable.getD i []).getD j 0

-- ══════════════════════════════════════════════════════════
-- THE TEN DISTINCT ENTRIES (each via the SSOT dimension formula)
-- ══════════════════════════════════════════════════════════

theorem entry_RR : lieAlgebraDim .A 1 = 3 := by decide      -- A₁ = so(3)
theorem entry_RC : lieAlgebraDim .A 2 = 8 := by decide      -- A₂ = su(3)
theorem entry_RH : lieAlgebraDim .C 3 = 21 := by decide     -- C₃ = sp(3)
theorem entry_RO : lieAlgebraDim .F4 4 = 52 := by decide    -- F₄
theorem entry_CC : 2 * lieAlgebraDim .A 2 = 16 := by decide -- A₂⊕A₂ = su(3)⊕su(3)
theorem entry_CH : lieAlgebraDim .A 5 = 35 := by decide     -- A₅ = su(6)
theorem entry_CO : lieAlgebraDim .E6 6 = 78 := by decide    -- E₆
theorem entry_HH : lieAlgebraDim .D 6 = 66 := by decide     -- D₆ = so(12)
theorem entry_HO : lieAlgebraDim .E7 7 = 133 := by decide   -- E₇
theorem entry_OO : lieAlgebraDim .E8 8 = 248 := by decide   -- E₈

/-- Every table cell matches its Dynkin-type dimension (and the (ℂ,ℂ) sum). -/
theorem table_matches_lie_dims :
    cell 0 0 = lieAlgebraDim .A 1 ∧ cell 0 1 = lieAlgebraDim .A 2
    ∧ cell 0 2 = lieAlgebraDim .C 3 ∧ cell 0 3 = lieAlgebraDim .F4 4
    ∧ cell 1 1 = 2 * lieAlgebraDim .A 2 ∧ cell 1 2 = lieAlgebraDim .A 5
    ∧ cell 1 3 = lieAlgebraDim .E6 6 ∧ cell 2 2 = lieAlgebraDim .D 6
    ∧ cell 2 3 = lieAlgebraDim .E7 7 ∧ cell 3 3 = lieAlgebraDim .E8 8 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide

-- ══════════════════════════════════════════════════════════
-- SYMMETRY  +  OCTONION ROW
-- ══════════════════════════════════════════════════════════

/-- **The magic square is symmetric**: `M[i][j] = M[j][i]` over the 4×4 grid. -/
theorem magic_symmetric :
    (List.range 4).all (fun i => (List.range 4).all (fun j => cell i j == cell j i)) = true := by
  decide

/-- **The octonion row is the exceptional row** `F₄,E₆,E₇,E₈` = `52,78,133,248`
    (the row/col indexed by `divDims[3] = 8 = dim 𝕆`). -/
theorem octonion_row_is_exceptional :
    cell 3 0 = 52 ∧ cell 3 1 = 78 ∧ cell 3 2 = 133 ∧ cell 3 3 = 248
      ∧ divDims.getLastD 0 = 8 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- The diagonal `[3,16,66,248]` — the "split" division-algebra row entries. -/
theorem magic_diagonal :
    cell 0 0 = 3 ∧ cell 1 1 = 16 ∧ cell 2 2 = 66 ∧ cell 3 3 = 248 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

-- ══════════════════════════════════════════════════════════
-- MASTER CERTIFICATE
-- ══════════════════════════════════════════════════════════

/-- **THE FREUDENTHAL–TITS MAGIC SQUARE.** The symmetric 4×4 table of
    Lie-algebra dimensions over ℝ,ℂ,ℍ,𝕆 is symmetric, its ten distinct entries
    are `3,8,16,21,35,52,66,78,133,248`, and the octonion row is the exceptional
    series `F₄(52) → E₆(78) → E₇(133) → E₈(248)`. -/
theorem freudenthal_magic_square :
    -- symmetric
    ((List.range 4).all (fun i => (List.range 4).all (fun j => cell i j == cell j i)) = true)
    -- the ten distinct entries
    ∧ cell 0 0 = 3 ∧ cell 0 1 = 8 ∧ cell 0 2 = 21 ∧ cell 0 3 = 52
    ∧ cell 1 1 = 16 ∧ cell 1 2 = 35 ∧ cell 1 3 = 78
    ∧ cell 2 2 = 66 ∧ cell 2 3 = 133
    ∧ cell 3 3 = 248
    -- octonion row = exceptional row
    ∧ cell 3 0 = 52 ∧ cell 3 1 = 78 ∧ cell 3 2 = 133 ∧ cell 3 3 = 248 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide

end Gnosis.FreudenthalMagicSquare
