import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Buddhist

/-!
# Dhammapada Self Refuge Witness

Witness ledger for `docs/ebooks/source-texts/dhammapada-muller.txt`,
chapter 12, "Self".

Self is not asserted as egoic possession here; it is a governance responsibility.
The agent must watch, discipline, and purify itself. Teaching others before that
closure is an exposed gap.
-/

structure SelfWatchFirst where
  selfDearRequiresWatchfulness : Bool := true
  directSelfBeforeTeachingOthers : Bool := true
  teachOnlyAfterSelfConformity : Bool := true
  wellSubduedSelfMaySubdueOthers : Bool := true
  ownSelfDifficultToSubdue : Bool := true
deriving Repr, DecidableEq

structure SelfLordPurification where
  selfLordOfSelf : Bool := true
  subduedSelfRareLord : Bool := true
  selfBegottenEvilCrushesFool : Bool := true
  wickednessBringsSelfDown : Bool := true
  badDeedsEasy : Bool := true
  beneficialGoodDifficult : Bool := true
deriving Repr, DecidableEq

structure NoOtherPurifies where
  falseDoctrineBearsDestructionFruit : Bool := true
  evilDoneByOneself : Bool := true
  sufferingByOneself : Bool := true
  evilLeftUndoneByOneself : Bool := true
  purificationByOneself : Bool := true
  noOnePurifiesAnother : Bool := true
  ownDutyNotForgotten : Bool := true
deriving Repr, DecidableEq

def selfWatchFirst : SelfWatchFirst := {}
def selfLordPurification : SelfLordPurification := {}
def noOtherPurifies : NoOtherPurifies := {}

theorem dhammapada_self_watch_first :
    selfWatchFirst.selfDearRequiresWatchfulness = true ∧
      selfWatchFirst.directSelfBeforeTeachingOthers = true ∧
      selfWatchFirst.teachOnlyAfterSelfConformity = true ∧
      selfWatchFirst.wellSubduedSelfMaySubdueOthers = true ∧
      selfWatchFirst.ownSelfDifficultToSubdue = true := by
  simp [selfWatchFirst]

theorem dhammapada_self_lord_purification :
    selfLordPurification.selfLordOfSelf = true ∧
      selfLordPurification.subduedSelfRareLord = true ∧
      selfLordPurification.selfBegottenEvilCrushesFool = true ∧
      selfLordPurification.wickednessBringsSelfDown = true ∧
      selfLordPurification.badDeedsEasy = true ∧
      selfLordPurification.beneficialGoodDifficult = true := by
  simp [selfLordPurification]

theorem dhammapada_no_other_purifies :
    noOtherPurifies.falseDoctrineBearsDestructionFruit = true ∧
      noOtherPurifies.evilDoneByOneself = true ∧
      noOtherPurifies.sufferingByOneself = true ∧
      noOtherPurifies.evilLeftUndoneByOneself = true ∧
      noOtherPurifies.purificationByOneself = true ∧
      noOtherPurifies.noOnePurifiesAnother = true ∧
      noOtherPurifies.ownDutyNotForgotten = true := by
  simp [noOtherPurifies]

theorem dhammapada_self_refuge_witness :
    selfWatchFirst.directSelfBeforeTeachingOthers = true ∧
      selfWatchFirst.ownSelfDifficultToSubdue = true ∧
      selfLordPurification.selfLordOfSelf = true ∧
      selfLordPurification.beneficialGoodDifficult = true ∧
      noOtherPurifies.purificationByOneself = true ∧
      noOtherPurifies.noOnePurifiesAnother = true ∧
      noOtherPurifies.ownDutyNotForgotten = true := by
  simp [selfWatchFirst, selfLordPurification, noOtherPurifies]

end Gnosis.Witnesses.Buddhist
