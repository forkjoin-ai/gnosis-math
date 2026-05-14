import Gnosis.DiscreteModulusTactic

/-!
# Gnosis.DiscreteContinuumConstants

Nat-only footholds for constants that usually enter through continuum
analysis.  The module does not import `Real`; it records scaled rational
certificates, finite tables, and named promotion obligations.
-/

namespace Gnosis
namespace DiscreteContinuumConstants

/-! ## Shared scaled-rational carrier -/

/-- A positive-denominator rational shadow, intended to be read as
`numerator / denominator` without importing rational or real arithmetic. -/
structure ScaledRatio where
  numerator : Nat
  denominator : Nat
  denominatorPositive : 0 < denominator
  deriving Repr

/-- Floor a rational shadow at a fixed decimal scale. -/
def scaledFloor (scale : Nat) (r : ScaledRatio) : Nat :=
  r.numerator * scale / r.denominator

/-- Squared comparison that avoids square roots:
`lower^2 < radicand * denominator^2`. -/
def squareBelow (radicand : Nat) (r : ScaledRatio) : Bool :=
  decide (r.numerator * r.numerator <
    radicand * (r.denominator * r.denominator))

/-- Squared comparison that avoids square roots:
`radicand * denominator^2 < upper^2`. -/
def squareAbove (radicand : Nat) (r : ScaledRatio) : Bool :=
  decide (radicand * (r.denominator * r.denominator) <
    r.numerator * r.numerator)

/-! ## Discrete logarithm thresholds -/

/-- `powTower base k` is `base^k`, kept explicit for Init-only modules. -/
def powTower (base : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => powTower base k * base

/-- Bounded floor-log search: count how many powers `base^k` with
`k ≤ fuel` still fit below `input`. -/
def discreteLogFloorFuel (base input : Nat) : Nat → Nat
  | 0 => 0
  | fuel + 1 =>
      let previous := discreteLogFloorFuel base input fuel
      if powTower base (fuel + 1) ≤ input then fuel + 1 else previous

structure DiscreteLogCertificate where
  base : Nat
  input : Nat
  exponent : Nat
  lowerFits : powTower base exponent ≤ input
  upperExcludes : input < powTower base (exponent + 1)

def log2_1024_certificate : DiscreteLogCertificate :=
  { base := 2
  , input := 1024
  , exponent := 10
  , lowerFits := by discrete_modulus
  , upperExcludes := by discrete_modulus }

theorem discrete_log_base2_first_65_threshold_table :
    (List.range 64).all
      (fun i =>
        let n := i + 1
        decide
          (powTower 2 (discreteLogFloorFuel 2 n 6) ≤ n ∧
           n < powTower 2 (discreteLogFloorFuel 2 n 6 + 1))) = true := by
  discrete_modulus

theorem discrete_log_base3_exact_powers_to_six :
    (List.range 7).all
      (fun k => decide (discreteLogFloorFuel 3 (powTower 3 k) 6 = k)) = true := by
  discrete_modulus

/-! ## Euler-number foothold -/

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)

/-- Integer-scaled partial sum for `e = Σ 1/k!`.
Each summand is floored at the given scale. -/
def ePartialScaled (scale terms : Nat) : Nat :=
  (List.range (terms + 1)).foldl
    (fun acc k => acc + scale / factorial k)
    0

def eSixDecimalTenTerms : Nat :=
  ePartialScaled 1000000 10

theorem e_six_decimal_ten_terms_value :
    eSixDecimalTenTerms = 2718277 := by
  discrete_modulus

theorem e_partial_scaled_first_terms_monotone_table :
    (List.range 10).all
      (fun k => decide (ePartialScaled 1000000 k ≤ ePartialScaled 1000000 (k + 1)))
      = true := by
  discrete_modulus

/-! ## Pi foothold -/

def piLower333_106 : ScaledRatio :=
  { numerator := 333, denominator := 106, denominatorPositive := by discrete_modulus }

def piUpper355_113 : ScaledRatio :=
  { numerator := 355, denominator := 113, denominatorPositive := by discrete_modulus }

theorem pi_archimedean_scaled_bracket :
    scaledFloor 1000000 piLower333_106 = 3141509
    ∧ scaledFloor 1000000 piUpper355_113 = 3141592
    ∧ scaledFloor 1000000 piUpper355_113 -
        scaledFloor 1000000 piLower333_106 = 83 := by
  discrete_modulus

theorem pi_archimedean_rational_order :
    piLower333_106.numerator * piUpper355_113.denominator <
      piUpper355_113.numerator * piLower333_106.denominator := by
  discrete_modulus

/-! ## Square-root and golden-ratio footholds -/

def sqrtTwoLower239_169 : ScaledRatio :=
  { numerator := 239, denominator := 169, denominatorPositive := by discrete_modulus }

def sqrtTwoUpper577_408 : ScaledRatio :=
  { numerator := 577, denominator := 408, denominatorPositive := by discrete_modulus }

theorem sqrt_two_scaled_bracket :
    squareBelow 2 sqrtTwoLower239_169 = true
    ∧ squareAbove 2 sqrtTwoUpper577_408 = true
    ∧ scaledFloor 1000000 sqrtTwoLower239_169 = 1414201
    ∧ scaledFloor 1000000 sqrtTwoUpper577_408 = 1414215 := by
  discrete_modulus

def phiLower987_610 : ScaledRatio :=
  { numerator := 987, denominator := 610, denominatorPositive := by discrete_modulus }

def phiUpper1597_987 : ScaledRatio :=
  { numerator := 1597, denominator := 987, denominatorPositive := by discrete_modulus }

theorem phi_scaled_bracket :
    scaledFloor 1000000 phiLower987_610 = 1618032
    ∧ scaledFloor 1000000 phiUpper1597_987 = 1618034
    ∧ scaledFloor 1000000 phiUpper1597_987 -
        scaledFloor 1000000 phiLower987_610 = 2 := by
  discrete_modulus

/-! ## Continuum promotion boundary -/

/-- A named placeholder for the non-discrete theorem needed to promote a
scaled rational bracket into a continuum statement. -/
structure ContinuumPromotionObligation where
  constantName : String
  discreteLower : ScaledRatio
  discreteUpper : ScaledRatio
  promotionStatement : String

def piPromotionObligation : ContinuumPromotionObligation :=
  { constantName := "pi"
  , discreteLower := piLower333_106
  , discreteUpper := piUpper355_113
  , promotionStatement :=
      "Show 333/106 < Real.pi and Real.pi < 355/113 in the chosen analysis layer." }

def ePromotionObligation : ContinuumPromotionObligation :=
  { constantName := "e"
  , discreteLower :=
      { numerator := eSixDecimalTenTerms
      , denominator := 1000000
      , denominatorPositive := by discrete_modulus }
  , discreteUpper :=
      { numerator := 2718283
      , denominator := 1000000
      , denominatorPositive := by discrete_modulus }
  , promotionStatement :=
      "Show the factorial tail after ten terms is below six scaled units." }

theorem continuum_obligations_are_named :
    piPromotionObligation.constantName = "pi"
    ∧ ePromotionObligation.constantName = "e" := by
  discrete_modulus

end DiscreteContinuumConstants
end Gnosis
