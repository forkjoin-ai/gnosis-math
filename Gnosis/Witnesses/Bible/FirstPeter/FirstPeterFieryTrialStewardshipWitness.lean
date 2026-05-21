namespace Gnosis.Witnesses.Bible.FirstPeter
namespace FirstPeterFieryTrialStewardshipWitness

/-!
# 1 Peter 4 -- Suffering Mind, Manifold Grace, and Fiery Trial

Source slice: 1 Peter 4:1-19.

Chapter invariant: suffering in the flesh becomes a break with the old social
runtime. The past life is sufficient; the crowd calls non-participation strange,
but their astonishment is not the witness's measure.

Primary gap/counterproof: the end of all things does not authorize panic or
spectacle. It produces sobriety, prayer, fervent charity, hospitality without
grudge, and gifts stewarded as manifold grace.

Unseen sat: fiery trial is not strange when union with Christ is the frame.
Shame is inverted: suffering as a criminal is not glory, but suffering as a
Christian can glorify God while the soul is committed to a faithful Creator in
well doing.

No `sorry`, no new `axiom`.
-/

structure SufferingMind where
  christSufferingArmsMind : Bool := true
  pastGentileWillIsEnough : Bool := true
  riotNonParticipationLooksStrange : Bool := true
  livingAndDeadFaceReadyJudge : Bool := true
  deadMayLiveAccordingToGodInSpirit : Bool := true
deriving DecidableEq, Repr

def sufferingMind : SufferingMind := {}

def sufferingMindWitness (s : SufferingMind) : Prop :=
  s.christSufferingArmsMind = true ∧
  s.pastGentileWillIsEnough = true ∧
  s.riotNonParticipationLooksStrange = true ∧
  s.livingAndDeadFaceReadyJudge = true ∧
  s.deadMayLiveAccordingToGodInSpirit = true

structure ManifoldGraceStewardship where
  endProducesSoberPrayer : Bool := true
  charityCoversMultitude : Bool := true
  hospitalityWithoutGrudging : Bool := true
  giftsMinisterAsStewards : Bool := true
  speechAsOraclesOfGod : Bool := true
  ministryByGodGivenAbility : Bool := true
deriving DecidableEq, Repr

def manifoldGraceStewardship : ManifoldGraceStewardship := {}

def stewardshipWitness (m : ManifoldGraceStewardship) : Prop :=
  m.endProducesSoberPrayer = true ∧
  m.charityCoversMultitude = true ∧
  m.hospitalityWithoutGrudging = true ∧
  m.giftsMinisterAsStewards = true ∧
  m.speechAsOraclesOfGod = true ∧
  m.ministryByGodGivenAbility = true

structure FieryTrialCounterproof where
  fieryTrialNotStrange : Bool := true
  christSufferingSharedForRevealedGlory : Bool := true
  reproachCanRestGlorySpirit : Bool := true
  criminalSufferingNotConfusedWithChristianSuffering : Bool := true
  judgmentBeginsAtHouseOfGod : Bool := true
  soulsCommittedToFaithfulCreatorInWellDoing : Bool := true
deriving DecidableEq, Repr

def fieryTrialCounterproof : FieryTrialCounterproof := {}

def shameLedgerRejected (c : FieryTrialCounterproof) : Prop :=
  c.fieryTrialNotStrange = true ∧
  c.christSufferingSharedForRevealedGlory = true ∧
  c.reproachCanRestGlorySpirit = true ∧
  c.criminalSufferingNotConfusedWithChristianSuffering = true ∧
  c.judgmentBeginsAtHouseOfGod = true ∧
  c.soulsCommittedToFaithfulCreatorInWellDoing = true

theorem first_peter_suffering_mind :
    sufferingMindWitness sufferingMind := by
  unfold sufferingMindWitness sufferingMind
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem first_peter_stewardship :
    stewardshipWitness manifoldGraceStewardship := by
  unfold stewardshipWitness manifoldGraceStewardship
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_peter_shame_ledger_rejected :
    shameLedgerRejected fieryTrialCounterproof := by
  unfold shameLedgerRejected fieryTrialCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_peter_fiery_trial_stewardship_witness :
    sufferingMindWitness sufferingMind ∧
    stewardshipWitness manifoldGraceStewardship ∧
    shameLedgerRejected fieryTrialCounterproof := by
  exact ⟨first_peter_suffering_mind,
    first_peter_stewardship,
    first_peter_shame_ledger_rejected⟩

end FirstPeterFieryTrialStewardshipWitness
end Gnosis.Witnesses.Bible.FirstPeter
