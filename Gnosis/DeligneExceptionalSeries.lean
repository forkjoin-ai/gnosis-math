/-
  DeligneExceptionalSeries
  ========================

  The Deligne–Vogel exceptional series of simple Lie algebras

      A₁ ⊂ A₂ ⊂ G₂ ⊂ D₄ ⊂ F₄ ⊂ E₆ ⊂ E₇ ⊂ E₈

  (Deligne, *La série exceptionnelle de groupes de Lie*, C. R. Acad. Sci.
  1996; Vogel's universal Lie algebra; Cohen–de Man; Landsberg–Manivel).
  These eight algebras share a uniform decomposition of tensor powers of
  the adjoint representation: many invariant-theoretic quantities (Casimir
  eigenvalues, representation dimensions, the antisymmetric/symmetric square
  decomposition of g ⊗ g) are given by ONE rational formula in a single
  parameter.

  Their dimensions are

      dim A₁ =   3
      dim A₂ =   8
      dim G₂ =  14
      dim D₄ =  28
      dim F₄ =  52
      dim E₆ =  78
      dim E₇ = 133
      dim E₈ = 248

  and their dual Coxeter numbers h∨ are

      h∨ = [2, 3, 4, 6, 9, 12, 18, 30].

  WHAT IS PROVED HERE (init-only, kernel `decide`/`rfl`, zero axioms beyond
  `propext`):

    * Each dimension, computed from the single source of truth
      `lieAlgebraDim t n = 2·(#positive roots) + rank` of
      `OctavianCubicMagicSquare` / `DynkinCoxeterClassification`, where
      `#positive roots = n·h/2` (`h` = Coxeter number). In particular the
      newly-derived D₄ = 2·12 + 4 = 28.
    * The strict ascending chain 3 < 8 < 14 < 28 < 52 < 78 < 133 < 248.
    * The dual-Coxeter-number list [2,3,4,6,9,12,18,30], with each h∨
      verified against its defining arithmetic (A_n: n+1; D_n: 2n−2;
      G₂: 4; F₄: 9; E₆: 12; E₇: 18; E₈: 30). Note h∨ = h (Coxeter number)
      for the simply-laced members A,D,E but h∨ < h for the doubly- and
      triply-laced G₂ (h=6, h∨=4) and F₄ (h=12, h∨=9).
    * The octonion-row tie: the last four dimensions 52, 78, 133, 248
      coincide with the `OctavianCubicMagicSquare` Freudenthal–Tits values
      for F₄, E₆, E₇, E₈.

  CITED, NOT FORMALIZED (needs the actual representation theory / Mathlib):
  the Deligne uniform construction itself, Vogel's universal Lie algebra,
  and the single rational *Deligne dimension formula* in the parameter.
  That formula is genuinely rational in the parameter (e.g.
  `dim g / (h∨ + 1)` runs `1, 2, 14/5, 4, 26/5, 6, 7, 8` — NON-integral for
  G₂ and F₄), so it does NOT reduce to a clean closed form in h∨ on the
  integers; we therefore prove the dimension list, the h∨ list, and the
  ordering, and cite the construction. No claim of an identity is made that
  is not proved below.

  Init + `OctavianCubicMagicSquare` + `DynkinCoxeterClassification`.
  Zero `sorry`, zero new `axiom`, no `Classical`, no `native_decide`.
-/

import Gnosis.OctavianCubicMagicSquare
import Gnosis.DynkinCoxeterClassification

namespace Gnosis.DeligneExceptionalSeries

open DynkinCoxeterClassification

/-- Dimension of a simple Lie algebra: `2·(#positive roots) + rank`, the
    single source of truth shared with `OctavianCubicMagicSquare`. Defined
    as a local alias to avoid the `lieAlgebraDim` name clash between the two
    opened namespaces (both definitions are identical). -/
abbrev lieAlgebraDim (t : DynkinType) (n : Nat) : Nat :=
  Gnosis.OctavianCubicMagicSquare.lieAlgebraDim t n

-- ══════════════════════════════════════════════════════════
-- THE EIGHT DIMENSIONS  (from the SSOT 2·posRoots + rank)
-- ══════════════════════════════════════════════════════════
-- Each dim g is `lieAlgebraDim t n = 2·positiveRootCount t n + n`, and
-- `positiveRootCount t n = n · coxeterNumber t n / 2`.

theorem dim_A1 : lieAlgebraDim .A 1 = 3 := by decide
theorem dim_A2 : lieAlgebraDim .A 2 = 8 := by decide
theorem dim_G2 : lieAlgebraDim .G2 2 = 14 := by decide
/-- D₄ = 2·12 + 4 = 28: D₄ has 12 positive roots (coxeterNumber .D 4 = 6,
    so 4·6/2 = 12) and rank 4. -/
theorem dim_D4 : lieAlgebraDim .D 4 = 28 := by decide
theorem dim_F4 : lieAlgebraDim .F4 4 = 52 := by decide
theorem dim_E6 : lieAlgebraDim .E6 6 = 78 := by decide
theorem dim_E7 : lieAlgebraDim .E7 7 = 133 := by decide
theorem dim_E8 : lieAlgebraDim .E8 8 = 248 := by decide

/-- D₄'s positive-root count is 12, and its Coxeter number is 6 — the
    arithmetic behind D₄ = 2·12 + 4 = 28. -/
theorem D4_posroots_12 :
    positiveRootCount .D 4 = 12 ∧ coxeterNumber .D 4 = 6 := by decide

/-- The ordered list of Deligne-series dimensions. -/
def deligneDims : List Nat :=
  [ lieAlgebraDim .A 1, lieAlgebraDim .A 2, lieAlgebraDim .G2 2,
    lieAlgebraDim .D 4, lieAlgebraDim .F4 4, lieAlgebraDim .E6 6,
    lieAlgebraDim .E7 7, lieAlgebraDim .E8 8 ]

theorem deligne_dims_values :
    deligneDims = [3, 8, 14, 28, 52, 78, 133, 248] := by decide

-- ══════════════════════════════════════════════════════════
-- STRICT ASCENDING CHAIN  3 < 8 < 14 < 28 < 52 < 78 < 133 < 248
-- ══════════════════════════════════════════════════════════

theorem deligne_chain_ascending :
    lieAlgebraDim .A 1 < lieAlgebraDim .A 2
    ∧ lieAlgebraDim .A 2 < lieAlgebraDim .G2 2
    ∧ lieAlgebraDim .G2 2 < lieAlgebraDim .D 4
    ∧ lieAlgebraDim .D 4 < lieAlgebraDim .F4 4
    ∧ lieAlgebraDim .F4 4 < lieAlgebraDim .E6 6
    ∧ lieAlgebraDim .E6 6 < lieAlgebraDim .E7 7
    ∧ lieAlgebraDim .E7 7 < lieAlgebraDim .E8 8 := by decide

/-- Strictly-sorted predicate for a `List Nat` (init-only; no Mathlib
    `List.Chain'`): every adjacent pair is strictly increasing. -/
def StrictSorted : List Nat → Bool
  | []           => true
  | [_]          => true
  | a :: b :: rest => (a < b) && StrictSorted (b :: rest)

/-- The explicit dimension list is strictly sorted. -/
theorem deligne_dims_strictly_sorted :
    StrictSorted deligneDims = true := by decide

-- ══════════════════════════════════════════════════════════
-- DUAL COXETER NUMBERS  h∨ = [2,3,4,6,9,12,18,30]
-- ══════════════════════════════════════════════════════════
-- h∨ equals the ordinary Coxeter number h for the simply-laced types
-- (A, D, E) but is strictly smaller for the non-simply-laced G₂ and F₄.
--   A_n: h∨ = n + 1     D_n: h∨ = 2n − 2
--   G₂:  h∨ = 4 (h = 6) F₄:  h∨ = 9 (h = 12)
--   E₆:  12   E₇: 18    E₈: 30

def dualCoxeterNumber : DynkinType → Nat → Nat
  | .A,  n => n + 1
  | .B,  n => 2 * n - 1
  | .C,  n => n + 1
  | .D,  n => 2 * n - 2
  | .E6, _ => 12
  | .E7, _ => 18
  | .E8, _ => 30
  | .F4, _ => 9
  | .G2, _ => 4

theorem dual_coxeter_A1 : dualCoxeterNumber .A 1 = 2 := by decide
theorem dual_coxeter_A2 : dualCoxeterNumber .A 2 = 3 := by decide
theorem dual_coxeter_G2 : dualCoxeterNumber .G2 2 = 4 := by decide
theorem dual_coxeter_D4 : dualCoxeterNumber .D 4 = 6 := by decide
theorem dual_coxeter_F4 : dualCoxeterNumber .F4 4 = 9 := by decide
theorem dual_coxeter_E6 : dualCoxeterNumber .E6 6 = 12 := by decide
theorem dual_coxeter_E7 : dualCoxeterNumber .E7 7 = 18 := by decide
theorem dual_coxeter_E8 : dualCoxeterNumber .E8 8 = 30 := by decide

/-- The dual-Coxeter-number list of the Deligne series. -/
def deligneDualCoxeter : List Nat :=
  [ dualCoxeterNumber .A 1, dualCoxeterNumber .A 2, dualCoxeterNumber .G2 2,
    dualCoxeterNumber .D 4, dualCoxeterNumber .F4 4, dualCoxeterNumber .E6 6,
    dualCoxeterNumber .E7 7, dualCoxeterNumber .E8 8 ]

theorem deligne_dual_coxeter_values :
    deligneDualCoxeter = [2, 3, 4, 6, 9, 12, 18, 30] := by decide

/-- h∨ also runs strictly increasing along the series. -/
theorem deligne_dual_coxeter_ascending :
    StrictSorted deligneDualCoxeter = true := by decide

/-- For the simply-laced members A,D,E the dual Coxeter number equals the
    ordinary Coxeter number; for G₂ and F₄ it is strictly smaller. -/
theorem dual_coxeter_vs_coxeter :
    dualCoxeterNumber .A 1 = coxeterNumber .A 1
    ∧ dualCoxeterNumber .A 2 = coxeterNumber .A 2
    ∧ dualCoxeterNumber .D 4 = coxeterNumber .D 4
    ∧ dualCoxeterNumber .E6 6 = coxeterNumber .E6 6
    ∧ dualCoxeterNumber .E7 7 = coxeterNumber .E7 7
    ∧ dualCoxeterNumber .E8 8 = coxeterNumber .E8 8
    ∧ dualCoxeterNumber .G2 2 < coxeterNumber .G2 2
    ∧ dualCoxeterNumber .F4 4 < coxeterNumber .F4 4 := by decide

-- ══════════════════════════════════════════════════════════
-- TIE TO THE OCTAVIAN CUBIC MAGIC SQUARE  (the octonion row)
-- ══════════════════════════════════════════════════════════
-- The last four members F₄, E₆, E₇, E₈ are exactly the octonion-row
-- (Freudenthal–Tits) algebras of `OctavianCubicMagicSquare`.

theorem deligne_tail_is_octonion_row :
    lieAlgebraDim .F4 4 = 52
    ∧ lieAlgebraDim .E6 6 = 78
    ∧ lieAlgebraDim .E7 7 = 133
    ∧ lieAlgebraDim .E8 8 = 248 := by decide

/-- The tail of the Deligne dimension list is the octonion row
    [52, 78, 133, 248]. -/
theorem deligne_tail_drop4 :
    deligneDims.drop 4 = [52, 78, 133, 248] := by decide

-- ══════════════════════════════════════════════════════════
-- MASTER CERTIFICATE
-- ══════════════════════════════════════════════════════════

/-- **DELIGNE EXCEPTIONAL SERIES.** The eight algebras
    A₁ ⊂ A₂ ⊂ G₂ ⊂ D₄ ⊂ F₄ ⊂ E₆ ⊂ E₇ ⊂ E₈ have dimensions
    [3,8,14,28,52,78,133,248] (each `2·posRoots + rank`), a strictly
    ascending chain, dual Coxeter numbers [2,3,4,6,9,12,18,30], and the
    tail [52,78,133,248] is the `OctavianCubicMagicSquare` octonion row.
    The uniform Deligne/Vogel construction and its rational dimension
    formula are cited, not formalized. -/
theorem deligne_exceptional_series :
    deligneDims = [3, 8, 14, 28, 52, 78, 133, 248]
    ∧ StrictSorted deligneDims = true
    ∧ deligneDualCoxeter = [2, 3, 4, 6, 9, 12, 18, 30]
    ∧ StrictSorted deligneDualCoxeter = true
    ∧ deligneDims.drop 4 = [52, 78, 133, 248] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Gnosis.DeligneExceptionalSeries
