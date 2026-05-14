import Gnosis.DiscreteContinuumConstants

/-!
# Gnosis.DiscreteContinuumConstantRefinement

Finite refinement towers for the Nat-only continuum footholds.  Each tower
records improving scaled brackets without importing `Real`.
-/

namespace Gnosis
namespace DiscreteContinuumConstantRefinement

open DiscreteContinuumConstants

/-! ## Generic bracket widths -/

structure ScaledBracket where
  lower : ScaledRatio
  upper : ScaledRatio
  deriving Repr

def scaledBracketLower (scale : Nat) (b : ScaledBracket) : Nat :=
  scaledFloor scale b.lower

def scaledBracketUpper (scale : Nat) (b : ScaledBracket) : Nat :=
  scaledFloor scale b.upper

def scaledBracketWidth (scale : Nat) (b : ScaledBracket) : Nat :=
  scaledBracketUpper scale b - scaledBracketLower scale b

/-! ## Euler-number refinement -/

def eBracketFiveTerms : ScaledBracket :=
  { lower :=
      { numerator := ePartialScaled 1000000 5
      , denominator := 1000000
      , denominatorPositive := by discrete_modulus }
  , upper :=
      { numerator := 2719000
      , denominator := 1000000
      , denominatorPositive := by discrete_modulus } }

def eBracketSevenTerms : ScaledBracket :=
  { lower :=
      { numerator := ePartialScaled 1000000 7
      , denominator := 1000000
      , denominatorPositive := by discrete_modulus }
  , upper :=
      { numerator := 2718300
      , denominator := 1000000
      , denominatorPositive := by discrete_modulus } }

def eBracketTenTerms : ScaledBracket :=
  { lower := ePromotionObligation.discreteLower
  , upper := ePromotionObligation.discreteUpper }

theorem e_refinement_widths_shrink :
    scaledBracketWidth 1000000 eBracketFiveTerms = 2335
    ∧ scaledBracketWidth 1000000 eBracketSevenTerms = 49
    ∧ scaledBracketWidth 1000000 eBracketTenTerms = 6
    ∧ scaledBracketWidth 1000000 eBracketTenTerms <
        scaledBracketWidth 1000000 eBracketSevenTerms
    ∧ scaledBracketWidth 1000000 eBracketSevenTerms <
        scaledBracketWidth 1000000 eBracketFiveTerms := by
  discrete_modulus

/-! ## Pi refinement -/

def piCoarse22_7 : ScaledBracket :=
  { lower := piLower333_106
  , upper :=
      { numerator := 22, denominator := 7, denominatorPositive := by discrete_modulus } }

def piArchimedeanBracket : ScaledBracket :=
  { lower := piLower333_106, upper := piUpper355_113 }

theorem pi_refinement_widths_shrink :
    scaledBracketWidth 1000000 piCoarse22_7 = 1348
    ∧ scaledBracketWidth 1000000 piArchimedeanBracket = 83
    ∧ scaledBracketWidth 1000000 piArchimedeanBracket <
        scaledBracketWidth 1000000 piCoarse22_7 := by
  discrete_modulus

/-! ## Square-root two refinement -/

def sqrtTwoCoarse99_70_140_99 : ScaledBracket :=
  { lower :=
      { numerator := 140, denominator := 99, denominatorPositive := by discrete_modulus }
  , upper :=
      { numerator := 99, denominator := 70, denominatorPositive := by discrete_modulus } }

def sqrtTwoPellBracket : ScaledBracket :=
  { lower := sqrtTwoLower239_169, upper := sqrtTwoUpper577_408 }

theorem sqrt_two_refinement_widths_shrink :
    scaledBracketWidth 1000000 sqrtTwoCoarse99_70_140_99 = 144
    ∧ scaledBracketWidth 1000000 sqrtTwoPellBracket = 14
    ∧ scaledBracketWidth 1000000 sqrtTwoPellBracket <
        scaledBracketWidth 1000000 sqrtTwoCoarse99_70_140_99
    ∧ squareBelow 2 sqrtTwoCoarse99_70_140_99.lower = true
    ∧ squareAbove 2 sqrtTwoCoarse99_70_140_99.upper = true := by
  discrete_modulus

/-! ## Golden-ratio refinement -/

def phiCoarse8_5_987_610 : ScaledBracket :=
  { lower :=
      { numerator := 8, denominator := 5, denominatorPositive := by discrete_modulus }
  , upper := phiUpper1597_987 }

def phiFibonacciBracket : ScaledBracket :=
  { lower := phiLower987_610, upper := phiUpper1597_987 }

theorem phi_refinement_widths_shrink :
    scaledBracketWidth 1000000 phiCoarse8_5_987_610 = 18034
    ∧ scaledBracketWidth 1000000 phiFibonacciBracket = 2
    ∧ scaledBracketWidth 1000000 phiFibonacciBracket <
        scaledBracketWidth 1000000 phiCoarse8_5_987_610 := by
  discrete_modulus

/-! ## Stack witness -/

theorem continuum_constant_refinement_stack_witness :
    scaledBracketWidth 1000000 eBracketTenTerms = 6
    ∧ scaledBracketWidth 1000000 piArchimedeanBracket = 83
    ∧ scaledBracketWidth 1000000 sqrtTwoPellBracket = 14
    ∧ scaledBracketWidth 1000000 phiFibonacciBracket = 2 := by
  discrete_modulus

/-! ## Machine-number target brackets -/

def piMachineTargetBracket : ScaledBracket :=
  { lower :=
      { numerator := 31415926535897932
      , denominator := 10000000000000000
      , denominatorPositive := by discrete_modulus }
  , upper :=
      { numerator := 31415926535897933
      , denominator := 10000000000000000
      , denominatorPositive := by discrete_modulus } }

def eMachineTargetBracket : ScaledBracket :=
  { lower :=
      { numerator := 27182818284590452
      , denominator := 10000000000000000
      , denominatorPositive := by discrete_modulus }
  , upper :=
      { numerator := 27182818284590453
      , denominator := 10000000000000000
      , denominatorPositive := by discrete_modulus } }

def sqrtTwoMachineTargetBracket : ScaledBracket :=
  { lower :=
      { numerator := 14142135623730950488
      , denominator := 10000000000000000000
      , denominatorPositive := by discrete_modulus }
  , upper :=
      { numerator := 14142135623730950489
      , denominator := 10000000000000000000
      , denominatorPositive := by discrete_modulus } }

def phiMachineTargetBracket : ScaledBracket :=
  { lower :=
      { numerator := 16180339887498948
      , denominator := 10000000000000000
      , denominatorPositive := by discrete_modulus }
  , upper :=
      { numerator := 16180339887498949
      , denominator := 10000000000000000
      , denominatorPositive := by discrete_modulus } }

theorem machine_target_brackets_are_ordered :
    piMachineTargetBracket.lower.numerator *
        piMachineTargetBracket.upper.denominator <
      piMachineTargetBracket.upper.numerator *
        piMachineTargetBracket.lower.denominator
    ∧ eMachineTargetBracket.lower.numerator *
        eMachineTargetBracket.upper.denominator <
      eMachineTargetBracket.upper.numerator *
        eMachineTargetBracket.lower.denominator
    ∧ sqrtTwoMachineTargetBracket.lower.numerator *
        sqrtTwoMachineTargetBracket.upper.denominator <
      sqrtTwoMachineTargetBracket.upper.numerator *
        sqrtTwoMachineTargetBracket.lower.denominator
    ∧ phiMachineTargetBracket.lower.numerator *
        phiMachineTargetBracket.upper.denominator <
      phiMachineTargetBracket.upper.numerator *
        phiMachineTargetBracket.lower.denominator := by
  discrete_modulus

theorem machine_target_brackets_refine_previous_widths :
    scaledBracketWidth 1000000 piMachineTargetBracket = 0
    ∧ scaledBracketWidth 1000000 eMachineTargetBracket = 0
    ∧ scaledBracketWidth 1000000 sqrtTwoMachineTargetBracket = 0
    ∧ scaledBracketWidth 1000000 phiMachineTargetBracket = 0 := by
  discrete_modulus

end DiscreteContinuumConstantRefinement
end Gnosis
