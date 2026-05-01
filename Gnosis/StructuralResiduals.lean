namespace Gnosis
namespace StructuralResiduals

/-- 
ResidualRecord represents the state residuals from a phase decomposition.
Any state boundary configuration produces a plus-phase and minus-phase residue.
-/
structure ResidualRecord where
  name : String
  plusResidue : Int
  minusResidue : Int
deriving Repr

/-! ## Manifestations -/

def cassini     : ResidualRecord :=
  { name := "Fibonacci Cassini F_{n-1}F_{n+1} - F_n²"
    plusResidue := 1, minusResidue := -1 }

def pell        : ResidualRecord :=
  { name := "Pell discriminant p_n² - 2 q_n²"
    plusResidue := 1, minusResidue := -1 }

def pisano      : ResidualRecord :=
  { name := "Pisano period phase (π | p ± 1)"
    plusResidue := 1, minusResidue := -1 }

def reciprocity : ResidualRecord :=
  { name := "Quadratic reciprocity sign"
    plusResidue := 1, minusResidue := -1 }

def writhe      : ResidualRecord :=
  { name := "Kauffman bracket writhe normalization"
    plusResidue := 1, minusResidue := -1 }

def towerDet    : ResidualRecord :=
  { name := "Tower determinant parity (Fib / Pell / CF)"
    plusResidue := 1, minusResidue := -1 }

def countBad    : ResidualRecord :=
  { name := "countBad_n vs L_n (Structural Outlier)"
    plusResidue := 2, minusResidue := -1 }

def catalog : List ResidualRecord :=
  [cassini, pell, pisano, reciprocity, writhe, towerDet, countBad]

/-! ## Counts -/

def countPlusExactlyOne : Nat :=
  catalog.foldl (fun n r => if r.plusResidue = 1 then n + 1 else n) 0

def countMinusExactlyNegOne : Nat :=
  catalog.foldl (fun n r => if r.minusResidue = -1 then n + 1 else n) 0

/-! ## Witnesses -/

theorem catalog_length : catalog.length = 7 := by rfl

theorem six_of_seven_plus_one : countPlusExactlyOne = 6 := by rfl

theorem seven_of_seven_minus_neg_one : countMinusExactlyNegOne = 7 := by rfl

theorem countBad_outlier_still_positive :
    countBad.plusResidue > 0 := by rfl

/-! ## Universal Structural Claims -/

/-- Every minus-residue in the catalog is exactly -1. -/
theorem all_minus_exactly_neg_one :
    catalog.all (fun r => r.minusResidue = -1) = true := by rfl

/-- Every plus-residue in the catalog is strictly positive. -/
theorem all_plus_strictly_positive :
    catalog.all (fun r => r.plusResidue > 0) = true := by rfl

/-- 
residual_master_witness:
Combined witness of structural residual invariants across the catalog.
-/
theorem residual_master_witness :
    catalog.length = 7 ∧
    catalog.all (fun r => r.minusResidue = -1) = true ∧
    catalog.all (fun r => r.plusResidue > 0) = true ∧
    countPlusExactlyOne = 6 ∧
    countBad.plusResidue = 2 := by
  simp [catalog, countPlusExactlyOne, countBad, cassini, pell, pisano, reciprocity, writhe, towerDet]

end StructuralResiduals
end Gnosis
