import Init

namespace Gnosis.Witnesses.Bible.SecondTimothy
namespace SecondTimothyUnboundWordWorkmanWitness

/-!
# 2 Timothy 2 -- Entrusted Men, Unbound Word, Approved Workman, Honorable Vessel

Source text: `docs/ebooks/source-texts/bible-kjv.txt:95630-95691`.

The chapter is transmission under hardship. The heard deposit is committed to
faithful teachers; the messenger is bound, but the word is not. The counterproof
is word-strife, canker speech, false resurrection claims, and unlearned questions.

No `sorry`, no new `axiom`.
-/

structure EnduringTransmission where
  strongInGrace : Bool := true
  heardAmongWitnessesCommittedToFaithful : Bool := true
  endureHardnessSoldier : Bool := true
  soldierNotEntangled : Bool := true
  lawfulStrivingCrowned : Bool := true
  laboringHusbandmanFirstFruits : Bool := true
  risenSeedDavidRemembered : Bool := true
  wordOfGodNotBound : Bool := true
  endureForElect : Bool := true
deriving DecidableEq, Repr

def enduringTransmission : EnduringTransmission := {}

def unboundWordWitness (t : EnduringTransmission) : Prop :=
  t.strongInGrace = true ∧
  t.heardAmongWitnessesCommittedToFaithful = true ∧
  t.endureHardnessSoldier = true ∧
  t.soldierNotEntangled = true ∧
  t.lawfulStrivingCrowned = true ∧
  t.laboringHusbandmanFirstFruits = true ∧
  t.risenSeedDavidRemembered = true ∧
  t.wordOfGodNotBound = true ∧
  t.endureForElect = true

structure ApprovedWorkmanVessel where
  faithfulSayingEndureReign : Bool := true
  wordStrifeSubvertsHearers : Bool := true
  rightlyDividingTruth : Bool := true
  vainBabblingCankerRejected : Bool := true
  falseResurrectionOverthrowsFaith : Bool := true
  foundationSealStandsSure : Bool := true
  vesselPurgedForHonor : Bool := true
  youthfulLustsFledVirtuesFollowed : Bool := true
  gentleMeekCorrectionForRecovery : Bool := true
deriving DecidableEq, Repr

def approvedWorkmanVessel : ApprovedWorkmanVessel := {}

def approvedWorkmanWitness (w : ApprovedWorkmanVessel) : Prop :=
  w.faithfulSayingEndureReign = true ∧
  w.wordStrifeSubvertsHearers = true ∧
  w.rightlyDividingTruth = true ∧
  w.vainBabblingCankerRejected = true ∧
  w.falseResurrectionOverthrowsFaith = true ∧
  w.foundationSealStandsSure = true ∧
  w.vesselPurgedForHonor = true ∧
  w.youthfulLustsFledVirtuesFollowed = true ∧
  w.gentleMeekCorrectionForRecovery = true

theorem second_timothy_unbound_word :
    unboundWordWitness enduringTransmission := by
  unfold unboundWordWitness enduringTransmission
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem second_timothy_approved_workman :
    approvedWorkmanWitness approvedWorkmanVessel := by
  unfold approvedWorkmanWitness approvedWorkmanVessel
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem second_timothy_unbound_word_workman_witness :
    unboundWordWitness enduringTransmission ∧
    approvedWorkmanWitness approvedWorkmanVessel := by
  exact ⟨second_timothy_unbound_word, second_timothy_approved_workman⟩

end SecondTimothyUnboundWordWorkmanWitness
end Gnosis.Witnesses.Bible.SecondTimothy
