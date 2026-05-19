import Gnosis.FiniteProbabilityCore.Events

namespace Gnosis
namespace FiniteProbabilityCore
/-! ## Conditioning -/

def conditionedWeights : List Nat → List Bool → List Nat
  | [], [] => []
  | [], _ :: _ => []
  | _ :: _, [] => []
  | weight :: weights, true :: mask => weight :: conditionedWeights weights mask
  | _weight :: weights, false :: mask => conditionedWeights weights mask

theorem conditionedWeights_total_eq_eventMass
    (weights : List Nat)
    (mask : List Bool) :
    sumNat (conditionedWeights weights mask) = eventMass weights mask := by
  induction weights generalizing mask with
  | nil =>
      cases mask <;> simp [conditionedWeights, eventMass, sumNat]
  | cons weight weights ih =>
      cases mask with
      | nil => simp [conditionedWeights, eventMass, sumNat]
      | cons selected mask =>
          cases selected
          · simp [conditionedWeights, eventMass, ih]
          · simp [conditionedWeights, eventMass, sumNat, ih]

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

end FiniteProbabilityCore
end Gnosis
