import Init

namespace Gnosis.Witnesses.Bible.Ephesians
namespace EphesiansUnityGiftMaturityWitness

/-!
# Ephesians 4:1-16 -- One Body, Ascension Gifts, and Mature Body Growth

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94152-94191`.

Unity is not flattening: one body and one Spirit hold differentiated gifts. The
goal is mature body growth, no longer doctrine-tossed children, but truth in
love compacted by every joint.

No `sorry`, no new `axiom`.
-/

structure UnityOfSpirit where
  worthyWalk : Bool := true
  lowlinessMeeknessLongsuffering : Bool := true
  forbearingInLove : Bool := true
  unitySpiritBondPeace : Bool := true
  oneBodySpiritHope : Bool := true
  oneLordFaithBaptism : Bool := true
  oneGodFatherAll : Bool := true
deriving DecidableEq, Repr

def unityOfSpirit : UnityOfSpirit := {}

def unityWitness (u : UnityOfSpirit) : Prop :=
  u.worthyWalk = true ∧ u.lowlinessMeeknessLongsuffering = true ∧
  u.forbearingInLove = true ∧ u.unitySpiritBondPeace = true ∧
  u.oneBodySpiritHope = true ∧ u.oneLordFaithBaptism = true ∧
  u.oneGodFatherAll = true

structure GiftMaturity where
  graceByMeasureOfGift : Bool := true
  ascendedAndDescended : Bool := true
  gaveMinistryGifts : Bool := true
  saintsPerfectedForMinistry : Bool := true
  unityFaithKnowledgeMature : Bool := true
  noLongerDoctrineTossed : Bool := true
  truthInLoveGrowth : Bool := true
  bodyCompactedByEveryJoint : Bool := true
deriving DecidableEq, Repr

def giftMaturity : GiftMaturity := {}

def maturityWitness (m : GiftMaturity) : Prop :=
  m.graceByMeasureOfGift = true ∧ m.ascendedAndDescended = true ∧
  m.gaveMinistryGifts = true ∧ m.saintsPerfectedForMinistry = true ∧
  m.unityFaithKnowledgeMature = true ∧ m.noLongerDoctrineTossed = true ∧
  m.truthInLoveGrowth = true ∧ m.bodyCompactedByEveryJoint = true

theorem ephesians_unity :
    unityWitness unityOfSpirit := by
  unfold unityWitness unityOfSpirit
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ephesians_maturity :
    maturityWitness giftMaturity := by
  unfold maturityWitness giftMaturity
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ephesians_unity_gift_maturity_witness :
    unityWitness unityOfSpirit ∧ maturityWitness giftMaturity := by
  exact ⟨ephesians_unity, ephesians_maturity⟩

end EphesiansUnityGiftMaturityWitness
end Gnosis.Witnesses.Bible.Ephesians
