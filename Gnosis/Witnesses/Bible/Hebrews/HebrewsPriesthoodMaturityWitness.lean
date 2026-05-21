namespace Gnosis.Witnesses.Bible.Hebrews
namespace HebrewsPriesthoodMaturityWitness

/-!
# Hebrews 5 -- Called Priesthood and Dull Hearing

Source slice: Hebrews 5:1-14.

Chapter invariant: priesthood is not self-assigned honor. The priest is called
of God, able to have compassion because he knows infirmity, and in Christ's case
is named Son and priest forever after Melchisedec while obedience is learned
through suffered flesh.

Primary gap/counterproof: sonship does not cancel obedience, and office does not
come by self-glorification. The chapter rejects both a prestige priesthood and a
static maturity claim: hearers who should teach can regress to milk when their
hearing dulls.

Unseen sat: Melchisedec is not merely a typology puzzle; he is the pressure test
for trained perception. Strong meat belongs to senses exercised by use to
discern good and evil.

No `sorry`, no new `axiom`.
-/

structure CalledPriesthood where
  priestTakenFromAmongMen : Bool := true
  compassionComesThroughInfirmity : Bool := true
  honourRequiresDivineCalling : Bool := true
  christDoesNotGlorifyHimself : Bool := true
  melchisedecOrderNamesForeverPriest : Bool := true
deriving DecidableEq, Repr

def calledPriesthood : CalledPriesthood := {}

def calledPriesthoodWitness (p : CalledPriesthood) : Prop :=
  p.priestTakenFromAmongMen = true ∧
  p.compassionComesThroughInfirmity = true ∧
  p.honourRequiresDivineCalling = true ∧
  p.christDoesNotGlorifyHimself = true ∧
  p.melchisedecOrderNamesForeverPriest = true

structure SufferingObedience where
  prayersAndTearsBelongToFleshDays : Bool := true
  sonLearnsObedienceThroughSuffering : Bool := true
  perfectedAuthorOfEternalSalvation : Bool := true
  obedienceMarksRecipients : Bool := true
deriving DecidableEq, Repr

def sufferingObedience : SufferingObedience := {}

def sufferingObedienceWitness (s : SufferingObedience) : Prop :=
  s.prayersAndTearsBelongToFleshDays = true ∧
  s.sonLearnsObedienceThroughSuffering = true ∧
  s.perfectedAuthorOfEternalSalvation = true ∧
  s.obedienceMarksRecipients = true

structure HearingMaturityCounterproof where
  dullHearingMakesHardSpeech : Bool := true
  teacherTimeCanRegressToMilk : Bool := true
  milkSignalsUnskilledRighteousnessWord : Bool := true
  strongMeatRequiresExercisedSenses : Bool := true
deriving DecidableEq, Repr

def hearingMaturityCounterproof : HearingMaturityCounterproof := {}

def dullHearingRejected (c : HearingMaturityCounterproof) : Prop :=
  c.dullHearingMakesHardSpeech = true ∧
  c.teacherTimeCanRegressToMilk = true ∧
  c.milkSignalsUnskilledRighteousnessWord = true ∧
  c.strongMeatRequiresExercisedSenses = true

theorem hebrews_called_priesthood :
    calledPriesthoodWitness calledPriesthood := by
  unfold calledPriesthoodWitness calledPriesthood
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_suffering_obedience :
    sufferingObedienceWitness sufferingObedience := by
  unfold sufferingObedienceWitness sufferingObedience
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem hebrews_dull_hearing_rejected :
    dullHearingRejected hearingMaturityCounterproof := by
  unfold dullHearingRejected hearingMaturityCounterproof
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem hebrews_priesthood_maturity_witness :
    calledPriesthoodWitness calledPriesthood ∧
    sufferingObedienceWitness sufferingObedience ∧
    dullHearingRejected hearingMaturityCounterproof := by
  exact ⟨hebrews_called_priesthood,
    hebrews_suffering_obedience,
    hebrews_dull_hearing_rejected⟩

end HebrewsPriesthoodMaturityWitness
end Gnosis.Witnesses.Bible.Hebrews
