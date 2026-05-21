namespace Gnosis.Witnesses.Bible.James
namespace JamesTestingDoingWitness

/-!
# James 1 -- Testing, Engrafted Word, and Doing

Source slice: James 1:1-27.

Chapter invariant: scattered faith is tested into wholeness. Trials are not
romanticized pain; they are the pressure by which patience is allowed to finish
its work so the person becomes entire rather than merely relieved.

Primary gap/counterproof: God is not the author of temptation, wealth is not
stability, anger is not righteousness, and hearing is not obedience. James opens
by cutting away the pious excuses that let a person blame God, trust status,
perform wrath, or admire the word without becoming it.

Unseen sat: the perfect law of liberty is a mirror that must become memory in
action. Pure religion is not the noise of unbridled speech; it is care for
fatherless and widows and remaining unspotted from the world.

No `sorry`, no new `axiom`.
-/

structure TestingPatience where
  trialsCanBeCountedJoy : Bool := true
  faithTestingWorksPatience : Bool := true
  patienceFinishesWholeness : Bool := true
  wisdomAskedInUnwaveringFaith : Bool := true
  doubleMindIsUnstable : Bool := true
deriving DecidableEq, Repr

def testingPatience : TestingPatience := {}

def testingPatienceWitness (t : TestingPatience) : Prop :=
  t.trialsCanBeCountedJoy = true ∧
  t.faithTestingWorksPatience = true ∧
  t.patienceFinishesWholeness = true ∧
  t.wisdomAskedInUnwaveringFaith = true ∧
  t.doubleMindIsUnstable = true

structure TemptationCounterproof where
  lowDegreeCanRejoiceInExaltation : Bool := true
  richManFadesLikeGrass : Bool := true
  godDoesNotTemptWithEvil : Bool := true
  lustConceivesSinAndDeath : Bool := true
  fatherOfLightsGivesGoodGifts : Bool := true
  wordOfTruthBegetsFirstfruits : Bool := true
deriving DecidableEq, Repr

def temptationCounterproof : TemptationCounterproof := {}

def falseTemptationLedgerRejected (c : TemptationCounterproof) : Prop :=
  c.lowDegreeCanRejoiceInExaltation = true ∧
  c.richManFadesLikeGrass = true ∧
  c.godDoesNotTemptWithEvil = true ∧
  c.lustConceivesSinAndDeath = true ∧
  c.fatherOfLightsGivesGoodGifts = true ∧
  c.wordOfTruthBegetsFirstfruits = true

structure EngraftedDoing where
  swiftHearingSlowsSpeechAndWrath : Bool := true
  humanWrathFailsGodsRighteousness : Bool := true
  engraftedWordSavesSoul : Bool := true
  hearerOnlyForgetsMirrorFace : Bool := true
  doerContinuesInLibertyLaw : Bool := true
  unbridledTongueMakesReligionVain : Bool := true
  pureReligionVisitsAfflictedAndKeepsUnspotted : Bool := true
deriving DecidableEq, Repr

def engraftedDoing : EngraftedDoing := {}

def engraftedDoingWitness (d : EngraftedDoing) : Prop :=
  d.swiftHearingSlowsSpeechAndWrath = true ∧
  d.humanWrathFailsGodsRighteousness = true ∧
  d.engraftedWordSavesSoul = true ∧
  d.hearerOnlyForgetsMirrorFace = true ∧
  d.doerContinuesInLibertyLaw = true ∧
  d.unbridledTongueMakesReligionVain = true ∧
  d.pureReligionVisitsAfflictedAndKeepsUnspotted = true

theorem james_testing_patience :
    testingPatienceWitness testingPatience := by
  unfold testingPatienceWitness testingPatience
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem james_false_temptation_ledger_rejected :
    falseTemptationLedgerRejected temptationCounterproof := by
  unfold falseTemptationLedgerRejected temptationCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem james_engrafted_doing :
    engraftedDoingWitness engraftedDoing := by
  unfold engraftedDoingWitness engraftedDoing
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem james_testing_doing_witness :
    testingPatienceWitness testingPatience ∧
    falseTemptationLedgerRejected temptationCounterproof ∧
    engraftedDoingWitness engraftedDoing := by
  exact ⟨james_testing_patience,
    james_false_temptation_ledger_rejected,
    james_engrafted_doing⟩

end JamesTestingDoingWitness
end Gnosis.Witnesses.Bible.James
