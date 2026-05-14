import Gnosis.DiscreteContinuumConstantRefinement

/-!
# Gnosis.DiscreteMachineNumberApproximation

Finite nearest-representable certificates for standard machine-number grids.
The module does not compute infinite expansions of constants.  It records the
finite binary32/binary64 cells that Rust, TypeScript, and Java use for common
constants, plus the midpoint boundaries that make the chosen cell inevitable
once the continuum layer supplies containment in that interval.
-/

namespace Gnosis
namespace DiscreteMachineNumberApproximation

open DiscreteContinuumConstants

/-! ## Generic midpoint certificate -/

/-- A finite binary-grid cell.  The represented value is
`significand / denominator`. -/
structure MachineCell where
  significand : Nat
  denominator : Nat
  denominatorPositive : 0 < denominator
  deriving Repr

/-- Midpoint boundaries around a candidate cell, represented at doubled
precision so no rational type is needed:

* lower midpoint: `(2 * significand - 1) / (2 * denominator)`
* upper midpoint: `(2 * significand + 1) / (2 * denominator)`
-/
structure NearestMachineCertificate where
  formatName : String
  constantName : String
  cell : MachineCell
  lowerMidpointTwice : Nat
  upperMidpointTwice : Nat
  lowerMidpointShape :
    lowerMidpointTwice + 1 = 2 * cell.significand
  upperMidpointShape :
    upperMidpointTwice = 2 * cell.significand + 1
  midpointGapIsOneUlp :
    upperMidpointTwice - lowerMidpointTwice = 2
  deriving Repr

/-- The later non-discrete proof obligation: show the named constant, when
scaled by `2 * denominator`, lies strictly between the two midpoint numerators. -/
structure MachinePromotionObligation where
  certificate : NearestMachineCertificate
  containmentStatement : String
  deriving Repr

/-! ## Binary64: Rust `f64`, TypeScript `number`, Java `double` -/

def binary64PiCell : MachineCell :=
  { significand := 7074237752028440
  , denominator := 2251799813685248
  , denominatorPositive := by discrete_modulus }

def binary64ECell : MachineCell :=
  { significand := 6121026514868073
  , denominator := 2251799813685248
  , denominatorPositive := by discrete_modulus }

def binary64SqrtTwoCell : MachineCell :=
  { significand := 6369051672525773
  , denominator := 4503599627370496
  , denominatorPositive := by discrete_modulus }

def binary64PhiCell : MachineCell :=
  { significand := 7286977268806824
  , denominator := 4503599627370496
  , denominatorPositive := by discrete_modulus }

def binary64PiNearest : NearestMachineCertificate :=
  { formatName := "binary64/f64/Java double/TypeScript number"
  , constantName := "pi"
  , cell := binary64PiCell
  , lowerMidpointTwice := 14148475504056879
  , upperMidpointTwice := 14148475504056881
  , lowerMidpointShape := by discrete_modulus
  , upperMidpointShape := by discrete_modulus
  , midpointGapIsOneUlp := by discrete_modulus }

def binary64ENearest : NearestMachineCertificate :=
  { formatName := "binary64/f64/Java double/TypeScript number"
  , constantName := "e"
  , cell := binary64ECell
  , lowerMidpointTwice := 12242053029736145
  , upperMidpointTwice := 12242053029736147
  , lowerMidpointShape := by discrete_modulus
  , upperMidpointShape := by discrete_modulus
  , midpointGapIsOneUlp := by discrete_modulus }

def binary64SqrtTwoNearest : NearestMachineCertificate :=
  { formatName := "binary64/f64/Java double/TypeScript number"
  , constantName := "sqrt2"
  , cell := binary64SqrtTwoCell
  , lowerMidpointTwice := 12738103345051545
  , upperMidpointTwice := 12738103345051547
  , lowerMidpointShape := by discrete_modulus
  , upperMidpointShape := by discrete_modulus
  , midpointGapIsOneUlp := by discrete_modulus }

def binary64PhiNearest : NearestMachineCertificate :=
  { formatName := "binary64/f64/Java double/TypeScript number"
  , constantName := "phi"
  , cell := binary64PhiCell
  , lowerMidpointTwice := 14573954537613647
  , upperMidpointTwice := 14573954537613649
  , lowerMidpointShape := by discrete_modulus
  , upperMidpointShape := by discrete_modulus
  , midpointGapIsOneUlp := by discrete_modulus }

theorem binary64_cells_are_standard_constants :
    binary64PiNearest.cell.significand = 7074237752028440
    ∧ binary64ENearest.cell.significand = 6121026514868073
    ∧ binary64SqrtTwoNearest.cell.significand = 6369051672525773
    ∧ binary64PhiNearest.cell.significand = 7286977268806824 := by
  discrete_modulus

theorem binary64_midpoint_gaps_are_one_ulp :
    binary64PiNearest.upperMidpointTwice -
        binary64PiNearest.lowerMidpointTwice = 2
    ∧ binary64ENearest.upperMidpointTwice -
        binary64ENearest.lowerMidpointTwice = 2
    ∧ binary64SqrtTwoNearest.upperMidpointTwice -
        binary64SqrtTwoNearest.lowerMidpointTwice = 2
    ∧ binary64PhiNearest.upperMidpointTwice -
        binary64PhiNearest.lowerMidpointTwice = 2 := by
  discrete_modulus

/-! ## Binary32: Rust `f32`, Java `float` -/

def binary32PiCell : MachineCell :=
  { significand := 13176795
  , denominator := 4194304
  , denominatorPositive := by discrete_modulus }

def binary32ECell : MachineCell :=
  { significand := 11401300
  , denominator := 4194304
  , denominatorPositive := by discrete_modulus }

def binary32SqrtTwoCell : MachineCell :=
  { significand := 11863283
  , denominator := 8388608
  , denominatorPositive := by discrete_modulus }

def binary32PhiCell : MachineCell :=
  { significand := 13573053
  , denominator := 8388608
  , denominatorPositive := by discrete_modulus }

def binary32PiNearest : NearestMachineCertificate :=
  { formatName := "binary32/f32/Java float"
  , constantName := "pi"
  , cell := binary32PiCell
  , lowerMidpointTwice := 26353589
  , upperMidpointTwice := 26353591
  , lowerMidpointShape := by discrete_modulus
  , upperMidpointShape := by discrete_modulus
  , midpointGapIsOneUlp := by discrete_modulus }

def binary32ENearest : NearestMachineCertificate :=
  { formatName := "binary32/f32/Java float"
  , constantName := "e"
  , cell := binary32ECell
  , lowerMidpointTwice := 22802599
  , upperMidpointTwice := 22802601
  , lowerMidpointShape := by discrete_modulus
  , upperMidpointShape := by discrete_modulus
  , midpointGapIsOneUlp := by discrete_modulus }

def binary32SqrtTwoNearest : NearestMachineCertificate :=
  { formatName := "binary32/f32/Java float"
  , constantName := "sqrt2"
  , cell := binary32SqrtTwoCell
  , lowerMidpointTwice := 23726565
  , upperMidpointTwice := 23726567
  , lowerMidpointShape := by discrete_modulus
  , upperMidpointShape := by discrete_modulus
  , midpointGapIsOneUlp := by discrete_modulus }

def binary32PhiNearest : NearestMachineCertificate :=
  { formatName := "binary32/f32/Java float"
  , constantName := "phi"
  , cell := binary32PhiCell
  , lowerMidpointTwice := 27146105
  , upperMidpointTwice := 27146107
  , lowerMidpointShape := by discrete_modulus
  , upperMidpointShape := by discrete_modulus
  , midpointGapIsOneUlp := by discrete_modulus }

theorem binary32_cells_are_standard_constants :
    binary32PiNearest.cell.significand = 13176795
    ∧ binary32ENearest.cell.significand = 11401300
    ∧ binary32SqrtTwoNearest.cell.significand = 11863283
    ∧ binary32PhiNearest.cell.significand = 13573053 := by
  discrete_modulus

/-! ## Promotion obligations -/

def binary64PiPromotion : MachinePromotionObligation :=
  { certificate := binary64PiNearest
  , containmentStatement :=
      "Show 14148475504056879 < 2 * 2251799813685248 * Real.pi and \
       2 * 2251799813685248 * Real.pi < 14148475504056881." }

def binary32PiPromotion : MachinePromotionObligation :=
  { certificate := binary32PiNearest
  , containmentStatement :=
      "Show 26353589 < 2 * 4194304 * Real.pi and \
       2 * 4194304 * Real.pi < 26353591." }

theorem standard_machine_pi_promotions_are_named :
    binary64PiPromotion.certificate.constantName = "pi"
    ∧ binary32PiPromotion.certificate.constantName = "pi" := by
  discrete_modulus

end DiscreteMachineNumberApproximation
end Gnosis
