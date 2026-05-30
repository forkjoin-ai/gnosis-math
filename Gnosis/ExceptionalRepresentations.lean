/-
  ExceptionalRepresentations
  ==========================

  The smallest nontrivial / minuscule representation dimensions of the
  exceptional Lie algebras, tied to the octonion-row data already proved in
  the Gnosis ledger.

  These dimensions are CITED representation-theory facts (the dimensions of
  the smallest faithful or minuscule representations of each exceptional
  type):

      G₂ :   7    smallest nontrivial rep (the imaginary octonions Im 𝕆)
      F₄ :  26    smallest nontrivial rep (the traceless Albert algebra)
      E₆ :  27    minuscule rep (the Albert algebra J₃(𝕆) itself)
      E₇ :  56    minuscule rep (the Freudenthal module)
      E₈ : 248    smallest faithful rep — which is the ADJOINT; E₈ has no
                  faithful representation smaller than its own dimension,
                  a property unique among the simple Lie algebras.

  What is PROVED here is the dimension arithmetic and the structural ties to
  the single sources of truth:

    * `DynkinCoxeterClassification.fundamentalDim` (E₇ ↦ 56, E₈ ↦ 248, …)
    * `OctavianCubicMagicSquare.albertDim` (= 27) and `octonionDim` (= 8)
    * `OctavianCubicMagicSquare.lieAlgebraDim` (the E-series dimensions)
    * `E8Lattice.cosetTower` (= [240, 56, 27, 16, 120])

  Specifically:
    * 7  = octonionDim − 1            (G₂ rep = imaginary octonions)
    * 26 = albertDim − 1   (= 27−1)   (F₄ rep = traceless Albert algebra)
    * 27 = albertDim       = cosetTower[2]  (E₆ minuscule = |E₆/D₅| factor)
    * 56 = fundamentalDim .E7 = cosetTower[1]  (E₇ minuscule = |E₇/E₆| factor)
    * 248 = lieAlgebraDim .E8 8       (E₈ minimal faithful = adjoint = the
                                       algebra dimension itself)
    * the ascending chain 7 < 26 < 27 < 56 < 248
    * the magic-square "rep" row F₄(26) ⊂ E₆(27) ⊂ E₇(56) ⊂ E₈(248).

  The fact that E₈'s minimal faithful representation equals its adjoint
  (248) is the one CITED special fact; the equality `248 = dim E₈` is
  what is proved against the SSOT.

  Init + `DynkinCoxeterClassification` + `OctavianCubicMagicSquare` +
  `E8Lattice`. NO Mathlib. Every theorem closes by kernel `decide`/`rfl`.
  Zero `sorry`, zero new `axiom`, no `native_decide`, no `Classical`.
-/

import Gnosis.DynkinCoxeterClassification
import Gnosis.OctavianCubicMagicSquare
import Gnosis.E8Lattice

namespace Gnosis.ExceptionalRepresentations

open DynkinCoxeterClassification
open Gnosis.OctavianCubicMagicSquare (albertDim octonionDim)

-- ══════════════════════════════════════════════════════════
-- THE SMALL-REP DIMENSIONS  (one tabulation, derived facts below)
-- ══════════════════════════════════════════════════════════

/-- Dimension of the smallest nontrivial / minuscule representation of an
    exceptional Lie algebra (for E₈ this is the smallest FAITHFUL rep, the
    adjoint). Tabulated; each value is justified against the SSOT below. -/
def smallRepDim : DynkinType → Nat
  | .G2 => 7
  | .F4 => 26
  | .E6 => 27
  | .E7 => 56
  | .E8 => 248
  | _   => 0

-- ══════════════════════════════════════════════════════════
-- G₂  :  7  =  octonionDim − 1   (the imaginary octonions)
-- ══════════════════════════════════════════════════════════

/-- **G₂ smallest nontrivial rep = 7.** It is realised as the imaginary
    octonions `Im 𝕆` = `𝕆 ⊖ ℝ`, dimension `8 − 1 = 7`. -/
theorem g2_rep_is_seven : smallRepDim .G2 = 7 := by decide

/-- **7 = octonionDim − 1.** The 7-dim G₂ module is the octonions minus
    their real line. -/
theorem g2_rep_eq_imaginary_octonions :
    smallRepDim .G2 = octonionDim - 1 := by decide

/-- The G₂ small rep matches the `fundamentalDim` SSOT tabulation. -/
theorem g2_rep_eq_fundamentalDim :
    smallRepDim .G2 = fundamentalDim .G2 := by decide

-- ══════════════════════════════════════════════════════════
-- F₄  :  26  =  albertDim − 1   (the traceless Albert algebra)
-- ══════════════════════════════════════════════════════════

/-- **F₄ smallest nontrivial rep = 26.** F₄ = Aut(J₃(𝕆)) acts on the
    traceless part of the Albert algebra, dimension `27 − 1 = 26`. -/
theorem f4_rep_is_twentysix : smallRepDim .F4 = 26 := by decide

/-- **26 = albertDim − 1 = 27 − 1.** The F₄ module is the traceless Albert
    algebra (this reuses `OctavianCubicMagicSquare.traceless_albert_26`). -/
theorem f4_rep_eq_traceless_albert :
    smallRepDim .F4 = albertDim - 1 := by decide

/-- The F₄ small rep matches the `fundamentalDim` SSOT tabulation. -/
theorem f4_rep_eq_fundamentalDim :
    smallRepDim .F4 = fundamentalDim .F4 := by decide

-- ══════════════════════════════════════════════════════════
-- E₆  :  27  =  albertDim  =  cosetTower[2]   (the Albert algebra)
-- ══════════════════════════════════════════════════════════

/-- **E₆ minuscule rep = 27.** It is the Albert algebra `J₃(𝕆)` itself,
    on which the cubic norm form is E₆-invariant. -/
theorem e6_rep_is_twentyseven : smallRepDim .E6 = 27 := by decide

/-- **27 = albertDim.** The E₆ minuscule module is the full Albert
    algebra. -/
theorem e6_rep_eq_albert :
    smallRepDim .E6 = albertDim := by decide

/-- **27 = cosetTower[2]**, the `|E₆/D₅|` factor of the E₈ Weyl coset
    tower `[240,56,27,16,120]`. -/
theorem e6_rep_is_coset_factor :
    E8Lattice.cosetTower[2]? = some (smallRepDim .E6) := by decide

/-- The E₆ small rep matches the `fundamentalDim` SSOT tabulation. -/
theorem e6_rep_eq_fundamentalDim :
    smallRepDim .E6 = fundamentalDim .E6 := by decide

-- ══════════════════════════════════════════════════════════
-- E₇  :  56  =  fundamentalDim .E7  =  cosetTower[1]   (Freudenthal)
-- ══════════════════════════════════════════════════════════

/-- **E₇ minuscule rep = 56.** It is the Freudenthal module (the
    Freudenthal triple system `56 = 1 + 27 + 27 + 1` over E₆). -/
theorem e7_rep_is_fiftysix : smallRepDim .E7 = 56 := by decide

/-- **56 = fundamentalDim .E7** — the SSOT minuscule dimension. -/
theorem e7_rep_eq_fundamentalDim :
    smallRepDim .E7 = fundamentalDim .E7 := by decide

/-- **56 = cosetTower[1]**, the `|E₇/E₆|` factor of the E₈ Weyl coset
    tower. -/
theorem e7_rep_is_coset_factor :
    E8Lattice.cosetTower[1]? = some (smallRepDim .E7) := by decide

/-- The Freudenthal module decomposes `56 = 1 + 27 + 27 + 1` over E₆
    (two Albert algebras plus two singlets). -/
theorem e7_rep_freudenthal_decomposition :
    smallRepDim .E7 = 1 + albertDim + albertDim + 1 := by decide

-- ══════════════════════════════════════════════════════════
-- E₈  :  248  =  lieAlgebraDim .E8 8   (the adjoint is the minimal rep)
-- ══════════════════════════════════════════════════════════

/-- **E₈ smallest faithful rep = 248.** Unique among the simple Lie
    algebras, E₈ has no faithful representation smaller than itself: the
    minimal faithful representation is the ADJOINT, dimension 248. -/
theorem e8_rep_is_248 : smallRepDim .E8 = 248 := by decide

/-- **248 = lieAlgebraDim .E8 8** — the minimal (faithful) E₈ rep equals
    the dimension of the algebra itself (the adjoint), using the SSOT
    `OctavianCubicMagicSquare.lieAlgebraDim`. -/
theorem e8_rep_eq_lie_algebra_dim :
    smallRepDim .E8 = Gnosis.OctavianCubicMagicSquare.lieAlgebraDim .E8 8 := by
  decide

/-- The same against the Dynkin-classification `lieAlgebraDim`
    (`rank + 2·#positive roots`), the original SSOT. -/
theorem e8_rep_eq_dynkin_lie_dim :
    smallRepDim .E8 = DynkinCoxeterClassification.lieAlgebraDim .E8 8 := by
  decide

/-- The E₈ minimal rep matches the `fundamentalDim` SSOT tabulation
    (which records 248 as both the smallest nontrivial and the adjoint). -/
theorem e8_rep_eq_fundamentalDim :
    smallRepDim .E8 = fundamentalDim .E8 := by decide

/-- E₈ self-duality of representation and algebra: the minimal rep, the
    `fundamentalDim`, and the algebra dimension all coincide at 248. -/
theorem e8_minimal_rep_is_adjoint :
    smallRepDim .E8 = fundamentalDim .E8
      ∧ smallRepDim .E8 = DynkinCoxeterClassification.lieAlgebraDim .E8 8 := by
  decide

-- ══════════════════════════════════════════════════════════
-- THE ASCENDING SMALL-REP CHAIN  7 < 26 < 27 < 56 < 248
-- ══════════════════════════════════════════════════════════

/-- **The small-rep chain is strictly ascending: 7 < 26 < 27 < 56 < 248.** -/
theorem small_rep_chain_ascending :
    smallRepDim .G2 < smallRepDim .F4
      ∧ smallRepDim .F4 < smallRepDim .E6
      ∧ smallRepDim .E6 < smallRepDim .E7
      ∧ smallRepDim .E7 < smallRepDim .E8 := by decide

/-- The explicit chain values, in order. -/
theorem small_rep_chain_values :
    [smallRepDim .G2, smallRepDim .F4, smallRepDim .E6,
     smallRepDim .E7, smallRepDim .E8] = [7, 26, 27, 56, 248] := by decide

-- ══════════════════════════════════════════════════════════
-- THE MAGIC-SQUARE OCTONION "REP" ROW
-- ══════════════════════════════════════════════════════════
-- The representation side of the octonion row of the Freudenthal–Tits
-- magic square: F₄ acts on 26, E₆ on 27, E₇ on 56, E₈ on its adjoint 248.
-- (The 26 ⊂ 27 inclusion is the traceless ⊂ full Albert algebra.)

/-- **The magic-square rep row F₄(26) ⊂ E₆(27) ⊂ E₇(56) ⊂ E₈(248).** Each
    representation embeds in the next: the traceless Albert algebra 26 sits
    inside the full Albert algebra 27 (the E₆ minuscule), which embeds in
    the Freudenthal 56 (the E₇ minuscule), which embeds in the E₈ adjoint
    248. This is the representation side of the octonion row. -/
theorem magic_square_rep_row :
    smallRepDim .F4 < smallRepDim .E6
      ∧ smallRepDim .E6 < smallRepDim .E7
      ∧ smallRepDim .E7 < smallRepDim .E8
      ∧ smallRepDim .E6 = albertDim
      ∧ smallRepDim .F4 = albertDim - 1
      ∧ smallRepDim .E7 = fundamentalDim .E7
      ∧ smallRepDim .E8 = fundamentalDim .E8 := by decide

/-- The 26 ⊂ 27 step is exactly traceless ⊂ full Albert algebra:
    `27 = 26 + 1`. -/
theorem f4_in_e6_traceless_step :
    smallRepDim .E6 = smallRepDim .F4 + 1 := by decide

-- ══════════════════════════════════════════════════════════
-- MASTER CERTIFICATE
-- ══════════════════════════════════════════════════════════

/-- **EXCEPTIONAL-SMALL-REPRESENTATIONS.** The smallest nontrivial /
    minuscule representation dimensions of the exceptional Lie algebras —
    G₂(7), F₄(26), E₆(27), E₇(56), E₈(248) — tied to the octonion-row SSOT:
    7 = octonionDim−1 (imaginary octonions), 26 = albertDim−1 (traceless
    Albert), 27 = albertDim = cosetTower[2] (Albert / |E₆/D₅|),
    56 = fundamentalDim .E7 = cosetTower[1] (Freudenthal / |E₇/E₆|),
    248 = dim E₈ (the minimal faithful rep is the adjoint); the chain
    7 < 26 < 27 < 56 < 248 is strictly ascending. -/
theorem exceptional_small_representations :
    smallRepDim .G2 = 7
    ∧ smallRepDim .F4 = 26
    ∧ smallRepDim .E6 = 27
    ∧ smallRepDim .E7 = 56
    ∧ smallRepDim .E8 = 248
    ∧ smallRepDim .G2 = octonionDim - 1
    ∧ smallRepDim .F4 = albertDim - 1
    ∧ smallRepDim .E6 = albertDim
    ∧ smallRepDim .E7 = fundamentalDim .E7
    ∧ smallRepDim .E8 = Gnosis.OctavianCubicMagicSquare.lieAlgebraDim .E8 8
    ∧ E8Lattice.cosetTower[2]? = some (smallRepDim .E6)
    ∧ E8Lattice.cosetTower[1]? = some (smallRepDim .E7)
    ∧ smallRepDim .G2 < smallRepDim .F4
    ∧ smallRepDim .F4 < smallRepDim .E6
    ∧ smallRepDim .E6 < smallRepDim .E7
    ∧ smallRepDim .E7 < smallRepDim .E8 := by decide

end Gnosis.ExceptionalRepresentations
