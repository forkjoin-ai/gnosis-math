import Gnosis.GnosisTriptychBraid

namespace Gnosis.Witnesses.Buddhist

/-!
# Dhammapada Wise Other Shore Witness

Witness ledger for `docs/ebooks/source-texts/dhammapada-muller.txt`,
chapter 6, "The Wise Man".

The wise person accepts correction, chooses noble friendship, fashions self as
craftsmen shape material, and crosses the dominion of death by practiced law.
-/

structure CorrectiveFriendship where
  wiseShowsTreasureAndAvoidance : Bool := true
  reproofBenefitsFollower : Bool := true
  admonitionBelovedByGood : Bool := true
  admonitionHatedByBad : Bool := true
  virtuousFriendsChosen : Bool := true
deriving Repr, DecidableEq

structure SelfFashioningSerenity where
  lawDrinkerSerene : Bool := true
  wellMakersLeadWater : Bool := true
  fletchersBendArrow : Bool := true
  carpentersBendWood : Bool := true
  wiseFashionThemselves : Bool := true
  rockNotShakenByWind : Bool := true
  deepStillLakeSerenity : Bool := true
deriving Repr, DecidableEq

structure OtherShorePassage where
  noUnfairSuccessDesired : Bool := true
  fewArriveOtherShore : Bool := true
  lawFollowersCrossDeathDominion : Bool := true
  darkStateLeftForBright : Bool := true
  pleasuresLeftBehind : Bool := true
  nothingCalledOwn : Bool := true
  freedomFromAttachmentInThisWorld : Bool := true
deriving Repr, DecidableEq

def correctiveFriendship : CorrectiveFriendship := {}
def selfFashioningSerenity : SelfFashioningSerenity := {}
def otherShorePassage : OtherShorePassage := {}

theorem dhammapada_corrective_friendship :
    correctiveFriendship.wiseShowsTreasureAndAvoidance = true ∧
      correctiveFriendship.reproofBenefitsFollower = true ∧
      correctiveFriendship.admonitionBelovedByGood = true ∧
      correctiveFriendship.admonitionHatedByBad = true ∧
      correctiveFriendship.virtuousFriendsChosen = true := by
  simp [correctiveFriendship]

theorem dhammapada_self_fashioning_serenity :
    selfFashioningSerenity.lawDrinkerSerene = true ∧
      selfFashioningSerenity.wellMakersLeadWater = true ∧
      selfFashioningSerenity.fletchersBendArrow = true ∧
      selfFashioningSerenity.carpentersBendWood = true ∧
      selfFashioningSerenity.wiseFashionThemselves = true ∧
      selfFashioningSerenity.rockNotShakenByWind = true ∧
      selfFashioningSerenity.deepStillLakeSerenity = true := by
  simp [selfFashioningSerenity]

theorem dhammapada_other_shore_passage :
    otherShorePassage.noUnfairSuccessDesired = true ∧
      otherShorePassage.fewArriveOtherShore = true ∧
      otherShorePassage.lawFollowersCrossDeathDominion = true ∧
      otherShorePassage.darkStateLeftForBright = true ∧
      otherShorePassage.pleasuresLeftBehind = true ∧
      otherShorePassage.nothingCalledOwn = true ∧
      otherShorePassage.freedomFromAttachmentInThisWorld = true := by
  simp [otherShorePassage]

theorem dhammapada_wise_other_shore_witness :
    correctiveFriendship.reproofBenefitsFollower = true ∧
      selfFashioningSerenity.wiseFashionThemselves = true ∧
      selfFashioningSerenity.deepStillLakeSerenity = true ∧
      otherShorePassage.lawFollowersCrossDeathDominion = true ∧
      otherShorePassage.nothingCalledOwn = true ∧
      otherShorePassage.freedomFromAttachmentInThisWorld = true := by
  simp [correctiveFriendship, selfFashioningSerenity, otherShorePassage]

end Gnosis.Witnesses.Buddhist
