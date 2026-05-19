import Gnosis.Witnesses.Buddhist.DhammacakkappavattanaWheelWitness

namespace Gnosis.Witnesses.Buddhist

/-! Witness ledger for Dhammapada chapter 14, "The Buddha". -/

structure AwakenedRefuge where
  awakenedTrackless : Bool := true
  desireSnareCannotLead : Bool := true
  noSinDoGoodPurifyMind : Bool := true
  nonStrikingAscetic : Bool := true
  lustsNotSatisfiedByGold : Bool := true
  unsafeFearRefuges : Bool := true
  fourTruthsSeen : Bool := true
  eightfoldWaySeen : Bool := true
  deliveredFromAllPain : Bool := true
deriving Repr, DecidableEq

def awakenedRefuge : AwakenedRefuge := {}

theorem dhammapada_awakened_refuge_witness :
    awakenedRefuge.awakenedTrackless = true ∧
      awakenedRefuge.desireSnareCannotLead = true ∧
      awakenedRefuge.noSinDoGoodPurifyMind = true ∧
      awakenedRefuge.nonStrikingAscetic = true ∧
      awakenedRefuge.unsafeFearRefuges = true ∧
      awakenedRefuge.fourTruthsSeen = true ∧
      awakenedRefuge.eightfoldWaySeen = true ∧
      awakenedRefuge.deliveredFromAllPain = true := by
  simp [awakenedRefuge]

end Gnosis.Witnesses.Buddhist
