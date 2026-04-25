import Init

/-!
# Universal Clinamen `+1`

Formalizes the first of two closing observations from this session:

> The `+1` really is universal. Seven independent phase reconstructions
> across seven different domains all carry `+1` as the plus-phase
> residue. Each dig was designed independently, and they agreed.

This module tabulates the plus-phase and minus-phase residues from the
seven phase-decomposition manifestations in
`GodFormulaPhaseManifestations`, plus one outlier (`countBad`), and
witnesses the universality claim decidably.

## Honest caveat

Six of seven manifestations carry plus-residue exactly `+1`. The
seventh (`countBad` vs `L_n`) carries plus-residue `+2`. The outlier
still has `minus-residue = −1` and a positive plus-residue, so the
clinamen direction is preserved; only its magnitude varies.

The stronger claim — "every plus-residue in the catalog is exactly
`+1`" — is false.

The weaker claim — "every catalogued minus-residue is exactly `−1`,
and every plus-residue is strictly positive" — is true, and
witnessed by `decide` below.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace BuleyeanMath
namespace UniversalClinamenPlusOne

structure ClinamenRecord where
  name : String
  plusResidue : Int
  minusResidue : Int
deriving Repr

/-! ## The seven records -/

def cassini     : ClinamenRecord :=
  { name := "Fibonacci Cassini F_{n-1}F_{n+1} - F_n²"
    plusResidue := 1, minusResidue := -1 }

def pell        : ClinamenRecord :=
  { name := "Pell discriminant p_n² - 2 q_n²"
    plusResidue := 1, minusResidue := -1 }

def pisano      : ClinamenRecord :=
  { name := "Pisano period phase (π | p ± 1)"
    plusResidue := 1, minusResidue := -1 }

def reciprocity : ClinamenRecord :=
  { name := "Quadratic reciprocity sign"
    plusResidue := 1, minusResidue := -1 }

def writhe      : ClinamenRecord :=
  { name := "Kauffman bracket writhe normalization"
    plusResidue := 1, minusResidue := -1 }

def towerDet    : ClinamenRecord :=
  { name := "Tower determinant parity (Fib / Pell / CF)"
    plusResidue := 1, minusResidue := -1 }

def countBad    : ClinamenRecord :=
  { name := "countBad_n vs L_n (outlier at +2)"
    plusResidue := 2, minusResidue := -1 }

def catalog : List ClinamenRecord :=
  [cassini, pell, pisano, reciprocity, writhe, towerDet, countBad]

/-! ## Counts -/

def countPlusExactlyOne : Nat :=
  catalog.foldl (fun n r => if r.plusResidue = 1 then n + 1 else n) 0

def countMinusExactlyNegOne : Nat :=
  catalog.foldl (fun n r => if r.minusResidue = -1 then n + 1 else n) 0

/-! ## Witnesses -/

theorem catalog_length : catalog.length = 7 := by decide

theorem six_of_seven_plus_one : countPlusExactlyOne = 6 := by decide

theorem seven_of_seven_minus_neg_one : countMinusExactlyNegOne = 7 := by decide

theorem countBad_outlier_magnitude :
    countBad.plusResidue = 2
    ∧ (2 : Int) ≠ 1 := by decide

theorem countBad_outlier_still_positive :
    countBad.plusResidue > 0 := by decide

/-! ## The weaker, true, universal claim

Every minus-residue is `−1`. Every plus-residue is strictly positive.
The outlier only varies the magnitude of the plus-residue; it does
not flip the sign. -/

theorem all_minus_exactly_neg_one :
    catalog.all (fun r => decide (r.minusResidue = -1)) = true := by decide

theorem all_plus_strictly_positive :
    catalog.all (fun r => decide (r.plusResidue > 0)) = true := by decide

/-! ## The stronger, false claim

For completeness, the stronger "every plus-residue is exactly `+1`"
claim FAILS because `countBad.plusResidue = 2`. Witnessed by
exhibiting the specific record that violates it. -/

theorem stronger_claim_fails_on_countBad :
    ¬ catalog.all (fun r => decide (r.plusResidue = 1)) = true := by decide

/-! ## Master witness -/

theorem universal_clinamen_master :
    catalog.length = 7
    -- Weaker claim: minus is always -1, plus is always positive
    ∧ catalog.all (fun r => decide (r.minusResidue = -1)) = true
    ∧ catalog.all (fun r => decide (r.plusResidue > 0)) = true
    -- Stronger claim: six of seven are exactly +1
    ∧ countPlusExactlyOne = 6
    -- Outlier is countBad at +2
    ∧ countBad.plusResidue = 2
    ∧ countBad.plusResidue > 0
    -- Stronger "all +1" claim fails
    ∧ ¬ catalog.all (fun r => decide (r.plusResidue = 1)) = true := by
  decide

/-! ## Reading

The clinamen's **sign** is universal across all seven independent
phase reconstructions. The clinamen's **magnitude** is `+1` in six
of seven and `+2` in the seventh.

The minus-phase residue is uniformly `−1`. The god formula's deficit
piece always subtracts exactly one unit from the raw identity; the
plus piece adds one (or, in the one outlier, two).

This module formalizes the honest version of "the `+1` is universal":
the direction is invariant, the magnitude is nearly invariant, and
the variance is catalogued as an outlier rather than hidden. A
stronger future formalization — proving that every future
phase-decomposition in this substrate must have plus-residue `+1` —
is not available at this scope; the outlier already rules it out.

What IS universal is the **direction**. Every clinamen pushes
forward; every deficit pulls back. The god formula's structure holds
across all catalogued digs in the substrate: one positive piece, one
negative piece, knit at the phase boundary.
-/

end UniversalClinamenPlusOne
end BuleyeanMath
