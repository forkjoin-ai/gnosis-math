import Gnosis.FiniteProbabilityCore.Conditioning

namespace Gnosis
namespace FiniteProbabilityCore
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
  deriving Repr

def ProductDistribution.productMass (product : ProductDistribution) : Nat :=
  product.left.totalMass * product.right.totalMass

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

end FiniteProbabilityCore
end Gnosis
