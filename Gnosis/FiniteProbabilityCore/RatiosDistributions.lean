import Init
import Gnosis.FiniteObserverCompactness
import Gnosis.FiniteObserverPatterns

namespace Gnosis
namespace FiniteProbabilityCore

/-!
# Finite Probability Core

Native finite probability for Gnosis. This module deliberately avoids Mathlib,
measure theory, real-valued probability, sigma algebras, and bridge objects.

Probability is represented by explicit finite supports with natural-number
weights. Probability values are exact numerator/denominator pairs.
-/

/-! ## Finite mass and exact ratios -/

def sumNat : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumNat xs

theorem sumNat_nil : sumNat [] = 0 := rfl

theorem sumNat_cons (x : Nat) (xs : List Nat) :
    sumNat (x :: xs) = x + sumNat xs := rfl

structure ProbabilityRatio where
  numerator : Nat
  denominator : Nat
  positiveDenominator : 0 < denominator
  deriving Repr

structure FiniteDistribution where
  weights : List Nat
  positiveTotal : 0 < sumNat weights
  deriving Repr

def FiniteDistribution.totalMass (distribution : FiniteDistribution) : Nat :=
  sumNat distribution.weights

theorem finite_distribution_total_positive
    (distribution : FiniteDistribution) :
    0 < distribution.totalMass :=
  distribution.positiveTotal

def singletonDistribution
    (mass : Nat)
    (hpositive : 0 < mass) : FiniteDistribution :=
  { weights := [mass]
    positiveTotal := by
      simp [sumNat]
      exact hpositive }

theorem singleton_distribution_total_mass
    (mass : Nat)
    (hpositive : 0 < mass) :
    (singletonDistribution mass hpositive).totalMass = mass := by
  simp [singletonDistribution, FiniteDistribution.totalMass, sumNat]

def probabilityRatio
    (num denom : Nat)
    (hdenom : 0 < denom) : ProbabilityRatio :=
  { numerator := num, denominator := denom, positiveDenominator := hdenom }

end FiniteProbabilityCore
end Gnosis
