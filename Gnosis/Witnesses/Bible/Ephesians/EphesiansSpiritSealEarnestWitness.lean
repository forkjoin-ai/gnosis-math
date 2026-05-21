import Init

namespace Gnosis.Witnesses.Bible.Ephesians
namespace EphesiansSpiritSealEarnestWitness

/-!
# Ephesians 1:13-14 -- Word of Truth, Spirit Seal, and Earnest Inheritance

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94039-94046`.

The hearing-believing-sealing sequence creates a custody marker that is not the
inheritance itself but the earnest until redemption of the purchased possession.

No `sorry`, no new `axiom`.
-/

structure GospelTrustSeal where
  wordOfTruthHeard : Bool := true
  gospelOfSalvationHeard : Bool := true
  trustedAfterHearing : Bool := true
  believedInChrist : Bool := true
  sealedWithHolySpiritOfPromise : Bool := true
deriving DecidableEq, Repr

def gospelTrustSeal : GospelTrustSeal := {}

def trustSealWitness (s : GospelTrustSeal) : Prop :=
  s.wordOfTruthHeard = true ∧
  s.gospelOfSalvationHeard = true ∧
  s.trustedAfterHearing = true ∧
  s.believedInChrist = true ∧
  s.sealedWithHolySpiritOfPromise = true

structure EarnestInheritance where
  spiritEarnestOfInheritance : Bool := true
  untilRedemptionOfPurchasedPossession : Bool := true
  untoPraiseOfGlory : Bool := true
deriving DecidableEq, Repr

def earnestInheritance : EarnestInheritance := {}

def earnestUntilRedemption (e : EarnestInheritance) : Prop :=
  e.spiritEarnestOfInheritance = true ∧
  e.untilRedemptionOfPurchasedPossession = true ∧
  e.untoPraiseOfGlory = true

theorem ephesians_trust_seal :
    trustSealWitness gospelTrustSeal := by
  unfold trustSealWitness gospelTrustSeal
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem ephesians_earnest_until_redemption :
    earnestUntilRedemption earnestInheritance := by
  unfold earnestUntilRedemption earnestInheritance
  exact ⟨rfl, rfl, rfl⟩

theorem ephesians_spirit_seal_earnest_witness :
    trustSealWitness gospelTrustSeal ∧
    earnestUntilRedemption earnestInheritance := by
  exact ⟨ephesians_trust_seal,
    ephesians_earnest_until_redemption⟩

end EphesiansSpiritSealEarnestWitness
end Gnosis.Witnesses.Bible.Ephesians
