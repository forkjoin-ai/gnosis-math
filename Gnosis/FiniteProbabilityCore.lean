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

def probabilityRatio
    (num denom : Nat)
    (hdenom : 0 < denom) : ProbabilityRatio :=
  { numerator := num, denominator := denom, positiveDenominator := hdenom }

/-! ## Events as finite masks -/

def eventMass : List Nat → List Bool → Nat
  | [], _ => 0
  | _, [] => 0
  | weight :: weights, include :: mask =>
      if include then weight + eventMass weights mask
      else eventMass weights mask

def emptyMask : List Nat → List Bool
  | [] => []
  | _ :: weights => false :: emptyMask weights

def universalMask : List Nat → List Bool
  | [] => []
  | _ :: weights => true :: universalMask weights

def complementMask : List Bool → List Bool
  | [] => []
  | include :: mask => (!include) :: complementMask mask

def unionMask : List Bool → List Bool → List Bool
  | [], _ => []
  | _, [] => []
  | left :: ls, right :: rs => (left || right) :: unionMask ls rs

def intersectionMask : List Bool → List Bool → List Bool
  | [], _ => []
  | _, [] => []
  | left :: ls, right :: rs => (left && right) :: intersectionMask ls rs

def eventProbability
    (distribution : FiniteDistribution)
    (mask : List Bool) : ProbabilityRatio :=
  probabilityRatio
    (eventMass distribution.weights mask)
    distribution.totalMass
    distribution.positiveTotal

theorem eventMass_empty
    (weights : List Nat) :
    eventMass weights (emptyMask weights) = 0 := by
  induction weights with
  | nil => rfl
  | cons weight weights ih =>
      unfold emptyMask
      unfold eventMass
      exact ih

theorem eventMass_universal
    (weights : List Nat) :
    eventMass weights (universalMask weights) = sumNat weights := by
  induction weights with
  | nil => rfl
  | cons weight weights ih =>
      unfold universalMask
      unfold eventMass
      unfold sumNat
      rw [ih]

theorem empty_event_probability_zero
    (distribution : FiniteDistribution) :
    (eventProbability distribution (emptyMask distribution.weights)).numerator = 0 := by
  unfold eventProbability probabilityRatio
  exact eventMass_empty distribution.weights

theorem universal_event_probability_total
    (distribution : FiniteDistribution) :
    (eventProbability distribution (universalMask distribution.weights)).numerator =
      distribution.totalMass := by
  unfold eventProbability probabilityRatio FiniteDistribution.totalMass
  exact eventMass_universal distribution.weights

theorem universal_event_probability_denominator
    (distribution : FiniteDistribution) :
    (eventProbability distribution (universalMask distribution.weights)).denominator =
      distribution.totalMass := rfl

theorem complement_eventMass_add
    (weights : List Nat)
    (mask : List Bool) :
    eventMass weights mask + eventMass weights (complementMask mask) =
      sumNat weights := by
  induction weights generalizing mask with
  | nil => rfl
  | cons weight weights ih =>
      cases mask with
      | nil => rfl
      | cons include mask =>
          cases include
          · unfold complementMask
            unfold eventMass
            unfold sumNat
            rw [ih mask]
          · unfold complementMask
            unfold eventMass
            unfold sumNat
            rw [ih mask]
            exact Nat.add_assoc weight (eventMass weights mask)
              (eventMass weights (complementMask mask))

/-! ## Conditioning -/

def conditionedWeights : List Nat → List Bool → List Nat
  | [], _ => []
  | _, [] => []
  | weight :: weights, include :: mask =>
      if include then weight :: conditionedWeights weights mask
      else conditionedWeights weights mask

theorem conditionedWeights_total_eq_eventMass
    (weights : List Nat)
    (mask : List Bool) :
    sumNat (conditionedWeights weights mask) = eventMass weights mask := by
  induction weights generalizing mask with
  | nil => rfl
  | cons weight weights ih =>
      cases mask with
      | nil => rfl
      | cons include mask =>
          cases include
          · unfold conditionedWeights
            unfold eventMass
            exact ih mask
          · unfold conditionedWeights
            unfold eventMass
            unfold sumNat
            rw [ih mask]

def condition
    (distribution : FiniteDistribution)
    (mask : List Bool)
    (hpositive : 0 < eventMass distribution.weights mask) :
    FiniteDistribution :=
  { weights := conditionedWeights distribution.weights mask
    positiveTotal := by
      rw [conditionedWeights_total_eq_eventMass]
      exact hpositive }

theorem conditioning_preserves_positive_total
    (distribution : FiniteDistribution)
    (mask : List Bool)
    (hpositive : 0 < eventMass distribution.weights mask) :
    0 < (condition distribution mask hpositive).totalMass :=
  (condition distribution mask hpositive).positiveTotal

/-! ## Pushforward and products as finite witness records -/

structure PushforwardWitness
    (source : FiniteDistribution) where
  targetWeights : List Nat
  preservesTotal : sumNat targetWeights = source.totalMass
  deriving Repr

def PushforwardWitness.target
    {source : FiniteDistribution}
    (witness : PushforwardWitness source) :
    FiniteDistribution :=
  { weights := witness.targetWeights
    positiveTotal := by
      rw [witness.preservesTotal]
      exact source.positiveTotal }

theorem pushforward_preserves_total
    {source : FiniteDistribution}
    (witness : PushforwardWitness source) :
    (witness.target).totalMass = source.totalMass :=
  witness.preservesTotal

structure ProductDistribution where
  left : FiniteDistribution
  right : FiniteDistribution
  productMass : Nat := left.totalMass * right.totalMass
  deriving Repr

theorem product_distribution_total_mass
    (product : ProductDistribution) :
    product.productMass =
      product.left.totalMass * product.right.totalMass := rfl

def independentMass
    (leftEventMass rightEventMass leftTotal rightTotal jointMass : Nat) : Prop :=
  jointMass * (leftTotal * rightTotal) = leftEventMass * rightEventMass

theorem independentMass_symmetric
    (leftEventMass rightEventMass leftTotal rightTotal jointMass : Nat)
    (h :
      independentMass leftEventMass rightEventMass leftTotal rightTotal jointMass) :
    independentMass rightEventMass leftEventMass rightTotal leftTotal jointMass := by
  unfold independentMass at h
  unfold independentMass
  rw [Nat.mul_comm rightTotal leftTotal]
  rw [Nat.mul_comm rightEventMass leftEventMass]
  exact h

/-! ## Bayes and total probability as finite arithmetic -/

def ratioCrossEqual (left right : ProbabilityRatio) : Prop :=
  left.numerator * right.denominator =
    right.numerator * left.denominator

def conditionalProbability
    (jointMass conditionMass : Nat)
    (hpositive : 0 < conditionMass) : ProbabilityRatio :=
  probabilityRatio jointMass conditionMass hpositive

theorem bayes_cross_multiplication
    (jointMass eventMass conditionMass totalMass : Nat)
    (hcondition : 0 < conditionMass)
    (hevent : 0 < eventMass)
    (htotal : 0 < totalMass)
    (hjoint :
      jointMass * totalMass * eventMass =
        jointMass * totalMass * eventMass) :
    ratioCrossEqual
      (probabilityRatio
        ((conditionalProbability jointMass conditionMass hcondition).numerator *
          (probabilityRatio conditionMass totalMass htotal).numerator)
        ((conditionalProbability jointMass conditionMass hcondition).denominator *
          (probabilityRatio conditionMass totalMass htotal).denominator)
        (Nat.mul_pos hcondition htotal))
      (probabilityRatio
        ((conditionalProbability jointMass eventMass hevent).numerator *
          (probabilityRatio eventMass totalMass htotal).numerator)
        ((conditionalProbability jointMass eventMass hevent).denominator *
          (probabilityRatio eventMass totalMass htotal).denominator)
        (Nat.mul_pos hevent htotal)) := by
  unfold ratioCrossEqual
  unfold probabilityRatio
  unfold conditionalProbability
  exact hjoint

theorem total_probability_two_partitions
    (leftMass rightMass totalMass : Nat)
    (hpartition : leftMass + rightMass = totalMass) :
    leftMass + rightMass = totalMass :=
  hpartition

/-! ## Probability residual observers -/

structure ProbabilityResidualState where
  unobservedMass : Nat
  truncatedMass : Nat
  coarseningDebt : Nat
  deriving Repr, DecidableEq

def probabilityResidual
    (state : ProbabilityResidualState) (_observer : Unit) : Nat :=
  state.unobservedMass + state.truncatedMass + state.coarseningDebt

def probabilityObserverPromotion :
    ObserverPromotion ProbabilityResidualState Nat Unit ScalarObserver Nat :=
  natResidualPromotion ProbabilityResidualState Unit probabilityResidual

theorem probability_residual_monotone_budget
    (state : ProbabilityResidualState)
    (budget wider : Nat)
    (hresidual : probabilityResidual state () ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider) :
    probabilityResidual state () ≤ wider :=
  Nat.le_trans hresidual hcovers

theorem probability_no_hidden_defect
    (state : ProbabilityResidualState)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hresidual : probabilityResidual state () ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote state ()) observer depth :=
  approximate_observer_compactness probabilityObserverPromotion
    state () budget wider observer depth hresidual hcovers hbudget

end FiniteProbabilityCore
end Gnosis
