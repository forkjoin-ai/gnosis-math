import Gnosis.FiniteProbabilityCore.RatiosDistributions

namespace Gnosis
namespace FiniteProbabilityCore
/-! ## Events as finite masks -/

def eventMass : List Nat → List Bool → Nat
  | [], [] => 0
  | [], _ :: _ => 0
  | _ :: _, [] => 0
  | weight :: weights, true :: mask => weight + eventMass weights mask
  | _weight :: weights, false :: mask => eventMass weights mask

def emptyMask : List Nat → List Bool
  | [] => []
  | _ :: weights => false :: emptyMask weights

def universalMask : List Nat → List Bool
  | [] => []
  | _ :: weights => true :: universalMask weights

def complementMaskFor : List Nat → List Bool → List Bool
  | [], _ => []
  | _ :: weights, [] => true :: complementMaskFor weights []
  | _ :: weights, true :: mask => false :: complementMaskFor weights mask
  | _ :: weights, false :: mask => true :: complementMaskFor weights mask

def unionMask : List Bool → List Bool → List Bool
  | [], _ => []
  | _, [] => []
  | left :: ls, right :: rs => (left || right) :: unionMask ls rs

def unionMaskFor : List Nat → List Bool → List Bool → List Bool
  | [], _, _ => []
  | _ :: weights, [], [] => false :: unionMaskFor weights [] []
  | _ :: weights, [], right :: rs => right :: unionMaskFor weights [] rs
  | _ :: weights, left :: ls, [] => left :: unionMaskFor weights ls []
  | _ :: weights, left :: ls, right :: rs =>
      (left || right) :: unionMaskFor weights ls rs

def intersectionMask : List Bool → List Bool → List Bool
  | [], _ => []
  | _, [] => []
  | left :: ls, right :: rs => (left && right) :: intersectionMask ls rs

def disjointMasks : List Bool → List Bool → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | left :: ls, right :: rs =>
      (!(left && right)) && disjointMasks ls rs

def exhaustiveMasks : List Nat → List Bool → List Bool → Bool
  | [], [], [] => true
  | [], _, _ => false
  | _ :: _, [], [] => false
  | _ :: weights, [], right :: rs =>
      right && exhaustiveMasks weights [] rs
  | _ :: weights, left :: ls, [] =>
      left && exhaustiveMasks weights ls []
  | _ :: weights, left :: ls, right :: rs =>
      (left || right) && exhaustiveMasks weights ls rs

theorem eventMass_union_empty_empty
    (weights : List Nat) :
    eventMass weights (unionMaskFor weights [] []) = 0 := by
  induction weights with
  | nil => simp [eventMass, unionMaskFor]
  | cons weight weights ih =>
      simp [eventMass, unionMaskFor, ih]

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
  | nil => simp [emptyMask, eventMass]
  | cons weight weights ih =>
      simp [emptyMask, eventMass, ih]

theorem eventMass_universal
    (weights : List Nat) :
    eventMass weights (universalMask weights) = sumNat weights := by
  induction weights with
  | nil => simp [universalMask, eventMass, sumNat]
  | cons weight weights ih =>
      simp [universalMask, eventMass, sumNat, ih]

theorem eventMass_complement_nil
    (weights : List Nat) :
    eventMass weights (complementMaskFor weights []) = sumNat weights := by
  induction weights with
  | nil => simp [eventMass, complementMaskFor, sumNat]
  | cons weight weights ih =>
      simp [eventMass, complementMaskFor, sumNat, ih]

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
    eventMass weights mask + eventMass weights (complementMaskFor weights mask) =
      sumNat weights := by
  induction weights generalizing mask with
  | nil =>
      cases mask <;> simp [eventMass, complementMaskFor, sumNat]
  | cons weight weights ih =>
      cases mask with
      | nil =>
          simp [eventMass, complementMaskFor, sumNat,
            eventMass_complement_nil]
      | cons selected mask =>
          cases selected
          · unfold eventMass
            unfold complementMaskFor
            unfold sumNat
            rw [Nat.add_left_comm]
            rw [ih mask]
          · unfold eventMass
            unfold complementMaskFor
            unfold sumNat
            rw [Nat.add_assoc]
            rw [ih mask]

theorem disjoint_union_eventMass_add
    (weights : List Nat)
    (left right : List Bool)
    (hdisjoint : disjointMasks left right = true) :
    eventMass weights (unionMaskFor weights left right) =
      eventMass weights left + eventMass weights right := by
  induction weights generalizing left right with
  | nil =>
      cases left <;> cases right <;> simp [eventMass, unionMaskFor]
  | cons weight weights ih =>
      cases left with
      | nil =>
          cases right with
          | nil => exact eventMass_union_empty_empty (weight :: weights)
          | cons rightSelected rs =>
              cases hdisjoint
      | cons leftSelected ls =>
          cases right with
          | nil => cases hdisjoint
          | cons rightSelected rs =>
              cases leftSelected <;> cases rightSelected
              · unfold disjointMasks at hdisjoint
                have htail : disjointMasks ls rs = true := hdisjoint
                unfold unionMaskFor
                unfold eventMass
                change eventMass weights (unionMaskFor weights ls rs) =
                  eventMass weights ls + eventMass weights rs
                exact ih ls rs htail
              · unfold disjointMasks at hdisjoint
                have htail : disjointMasks ls rs = true := hdisjoint
                unfold unionMaskFor
                unfold eventMass
                change weight + eventMass weights (unionMaskFor weights ls rs) =
                  eventMass weights ls + (weight + eventMass weights rs)
                rw [ih ls rs htail]
                exact Nat.add_left_comm weight (eventMass weights ls)
                  (eventMass weights rs)
              · unfold disjointMasks at hdisjoint
                have htail : disjointMasks ls rs = true := hdisjoint
                unfold unionMaskFor
                unfold eventMass
                change weight + eventMass weights (unionMaskFor weights ls rs) =
                  weight + eventMass weights ls + eventMass weights rs
                rw [ih ls rs htail]
                exact Eq.symm
                  (Nat.add_assoc weight (eventMass weights ls)
                    (eventMass weights rs))
              · unfold disjointMasks at hdisjoint
                cases hdisjoint

theorem exhaustive_union_eventMass_total
    (weights : List Nat)
    (left right : List Bool)
    (hexhaustive : exhaustiveMasks weights left right = true) :
    eventMass weights (unionMaskFor weights left right) = sumNat weights := by
  induction weights generalizing left right with
  | nil =>
      cases left <;> cases right <;> simp [eventMass, unionMaskFor, sumNat]
  | cons weight weights ih =>
      cases left with
      | nil =>
          cases right with
          | nil => cases hexhaustive
          | cons rightSelected rs =>
              cases rightSelected
              · unfold exhaustiveMasks at hexhaustive
                cases hexhaustive
              · unfold exhaustiveMasks at hexhaustive
                have htail : exhaustiveMasks weights [] rs = true := hexhaustive
                unfold unionMaskFor
                unfold eventMass
                unfold sumNat
                rw [ih [] rs htail]
      | cons leftSelected ls =>
          cases right with
          | nil =>
              cases leftSelected
              · unfold exhaustiveMasks at hexhaustive
                cases hexhaustive
              · unfold exhaustiveMasks at hexhaustive
                have htail : exhaustiveMasks weights ls [] = true := hexhaustive
                unfold unionMaskFor
                unfold eventMass
                unfold sumNat
                rw [ih ls [] htail]
          | cons rightSelected rs =>
              cases leftSelected <;> cases rightSelected
              · unfold exhaustiveMasks at hexhaustive
                cases hexhaustive
              · unfold exhaustiveMasks at hexhaustive
                have htail : exhaustiveMasks weights ls rs = true := hexhaustive
                simp [unionMaskFor, eventMass, sumNat, ih ls rs htail]
              · unfold exhaustiveMasks at hexhaustive
                have htail : exhaustiveMasks weights ls rs = true := hexhaustive
                simp [unionMaskFor, eventMass, sumNat, ih ls rs htail]
              · unfold exhaustiveMasks at hexhaustive
                have htail : exhaustiveMasks weights ls rs = true := hexhaustive
                simp [unionMaskFor, eventMass, sumNat, ih ls rs htail]

end FiniteProbabilityCore
end Gnosis
