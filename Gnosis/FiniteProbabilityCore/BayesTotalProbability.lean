import Gnosis.FiniteProbabilityCore.DistributionTransforms

namespace Gnosis
namespace FiniteProbabilityCore
/-! ## Bayes and total probability as finite arithmetic -/

def ratioCrossEqual (left right : ProbabilityRatio) : Prop :=
  left.numerator * right.denominator =
    right.numerator * left.denominator

def ratioMul (left right : ProbabilityRatio) : ProbabilityRatio :=
  probabilityRatio
    (left.numerator * right.numerator)
    (left.denominator * right.denominator)
    (Nat.mul_pos left.positiveDenominator right.positiveDenominator)

def conditionalProbability
    (jointMass conditionMass : Nat)
    (hpositive : 0 < conditionMass) : ProbabilityRatio :=
  probabilityRatio jointMass conditionMass hpositive

def partitionWeightedConditional
    (eventInPartMass partMass totalMass : Nat)
    (hpart : 0 < partMass)
    (htotal : 0 < totalMass) : ProbabilityRatio :=
  ratioMul
    (conditionalProbability eventInPartMass partMass hpart)
    (probabilityRatio partMass totalMass htotal)

def eventProbabilityFromMass
    (eventMass totalMass : Nat)
    (htotal : 0 < totalMass) : ProbabilityRatio :=
  probabilityRatio eventMass totalMass htotal

theorem partition_weighted_conditional_cross_equal
    (eventInPartMass partMass totalMass : Nat)
    (hpart : 0 < partMass)
    (htotal : 0 < totalMass) :
    ratioCrossEqual
      (partitionWeightedConditional eventInPartMass partMass totalMass hpart htotal)
      (eventProbabilityFromMass eventInPartMass totalMass htotal) := by
  unfold ratioCrossEqual
  unfold partitionWeightedConditional ratioMul conditionalProbability
  unfold eventProbabilityFromMass probabilityRatio
  exact Nat.mul_assoc eventInPartMass partMass totalMass

theorem total_probability_conditional_two_partition_masses
    (eventLeftMass eventRightMass leftMass rightMass totalMass : Nat)
    (hleft : 0 < leftMass)
    (hright : 0 < rightMass)
    (htotal : 0 < totalMass)
    (_hpartition : leftMass + rightMass = totalMass) :
    (partitionWeightedConditional eventLeftMass leftMass totalMass hleft htotal).numerator +
      (partitionWeightedConditional eventRightMass rightMass totalMass hright htotal).numerator =
        eventLeftMass * leftMass + eventRightMass * rightMass := by
  unfold partitionWeightedConditional ratioMul conditionalProbability probabilityRatio
  rfl

theorem bayes_cross_multiplication
    (jointMass eventMass conditionMass totalMass : Nat)
    (hcondition : 0 < conditionMass)
    (hevent : 0 < eventMass)
    (htotal : 0 < totalMass)
    (hjoint :
      (jointMass * conditionMass) * (eventMass * totalMass) =
        (jointMass * eventMass) * (conditionMass * totalMass)) :
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

theorem total_probability_of_disjoint_exhaustive_masks
    (distribution : FiniteDistribution)
    (left right : List Bool)
    (hdisjoint : disjointMasks left right = true)
    (hexhaustive : exhaustiveMasks distribution.weights left right = true) :
    eventMass distribution.weights left +
      eventMass distribution.weights right =
        distribution.totalMass := by
  rw [← disjoint_union_eventMass_add distribution.weights left right hdisjoint]
  rw [exhaustive_union_eventMass_total distribution.weights left right hexhaustive]
  rfl

theorem total_probability_conditional_two_partition_masks
    (distribution : FiniteDistribution)
    (eventLeft eventRight left right : List Bool)
    (hleft : 0 < eventMass distribution.weights left)
    (hright : 0 < eventMass distribution.weights right)
    (hdisjoint : disjointMasks left right = true)
    (hexhaustive : exhaustiveMasks distribution.weights left right = true) :
    (partitionWeightedConditional
        (eventMass distribution.weights eventLeft)
        (eventMass distribution.weights left)
        distribution.totalMass
        hleft
        distribution.positiveTotal).numerator +
      (partitionWeightedConditional
        (eventMass distribution.weights eventRight)
        (eventMass distribution.weights right)
        distribution.totalMass
        hright
        distribution.positiveTotal).numerator =
        eventMass distribution.weights eventLeft *
          eventMass distribution.weights left +
        eventMass distribution.weights eventRight *
          eventMass distribution.weights right := by
  exact total_probability_conditional_two_partition_masses
    (eventMass distribution.weights eventLeft)
    (eventMass distribution.weights eventRight)
    (eventMass distribution.weights left)
    (eventMass distribution.weights right)
    distribution.totalMass
    hleft
    hright
    distribution.positiveTotal
    (total_probability_of_disjoint_exhaustive_masks
      distribution left right hdisjoint hexhaustive)

end FiniteProbabilityCore
end Gnosis
