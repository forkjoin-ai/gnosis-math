import Gnosis.BuddhistAttachmentSkyrms

namespace Gnosis.Witnesses.Buddhist

/-!
# Dhammapada Evil Accumulation Witness

Witness ledger for `docs/ebooks/source-texts/dhammapada-muller.txt`,
chapter 9, "Evil".

This chapter turns karma into accumulation dynamics: good and evil ripen after
delay, small drops fill the pot, offense rebounds like dust against the wind,
and no spatial hiding place frees an agent from deed or death.
-/

structure RipeningAction where
  goodHastenedThoughtKeptFromEvil : Bool := true
  slothfulGoodLetsMindDelightInEvil : Bool := true
  repeatedSinRejected : Bool := true
  repeatedGoodApproved : Bool := true
  evilRipensToEvilSeen : Bool := true
  goodRipensToHappyDays : Bool := true
deriving Repr, DecidableEq

structure DropByDropPot where
  littleEvilNotDismissed : Bool := true
  waterDropsFillPot : Bool := true
  foolFullOfEvilLittleByLittle : Bool := true
  littleGoodNotDismissed : Bool := true
  wiseFullOfGoodLittleByLittle : Bool := true
deriving Repr, DecidableEq

structure NoHidingPlace where
  dangerousRoadAvoided : Bool := true
  unwoundedHandUnaffectedByPoison : Bool := true
  evilFallsBackLikeDustAgainstWind : Bool := true
  desireFreeAttainNirvana : Bool := true
  noPlaceFreeFromEvilDeed : Bool := true
  noPlaceDeathCannotOvercome : Bool := true
deriving Repr, DecidableEq

def ripeningAction : RipeningAction := {}
def dropByDropPot : DropByDropPot := {}
def noHidingPlace : NoHidingPlace := {}

theorem dhammapada_ripening_action :
    ripeningAction.goodHastenedThoughtKeptFromEvil = true ∧
      ripeningAction.slothfulGoodLetsMindDelightInEvil = true ∧
      ripeningAction.repeatedSinRejected = true ∧
      ripeningAction.repeatedGoodApproved = true ∧
      ripeningAction.evilRipensToEvilSeen = true ∧
      ripeningAction.goodRipensToHappyDays = true := by
  simp [ripeningAction]

theorem dhammapada_drop_by_drop_pot :
    dropByDropPot.littleEvilNotDismissed = true ∧
      dropByDropPot.waterDropsFillPot = true ∧
      dropByDropPot.foolFullOfEvilLittleByLittle = true ∧
      dropByDropPot.littleGoodNotDismissed = true ∧
      dropByDropPot.wiseFullOfGoodLittleByLittle = true := by
  simp [dropByDropPot]

theorem dhammapada_no_hiding_place :
    noHidingPlace.dangerousRoadAvoided = true ∧
      noHidingPlace.unwoundedHandUnaffectedByPoison = true ∧
      noHidingPlace.evilFallsBackLikeDustAgainstWind = true ∧
      noHidingPlace.desireFreeAttainNirvana = true ∧
      noHidingPlace.noPlaceFreeFromEvilDeed = true ∧
      noHidingPlace.noPlaceDeathCannotOvercome = true := by
  simp [noHidingPlace]

theorem dhammapada_evil_accumulation_witness :
    ripeningAction.evilRipensToEvilSeen = true ∧
      ripeningAction.goodRipensToHappyDays = true ∧
      dropByDropPot.waterDropsFillPot = true ∧
      dropByDropPot.foolFullOfEvilLittleByLittle = true ∧
      noHidingPlace.evilFallsBackLikeDustAgainstWind = true ∧
      noHidingPlace.noPlaceFreeFromEvilDeed = true ∧
      noHidingPlace.noPlaceDeathCannotOvercome = true := by
  simp [ripeningAction, dropByDropPot, noHidingPlace]

end Gnosis.Witnesses.Buddhist
