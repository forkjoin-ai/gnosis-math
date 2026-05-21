namespace Gnosis.Witnesses.Bible.Hebrews
namespace HebrewsFaithLedgerWitness

/-!
# Hebrews 11 -- Faith as the Witness Ledger of the Unseen

Source slice: Hebrews 11:1-40.

Chapter invariant: faith is not inferior evidence for people lacking proof; it
is the substance/evidence proper to things hoped for and not seen. Hebrews 11 is
therefore a ledger of agents who move before visibility catches up.

Primary gap/counterproof: visible possession is not the test of truth. Abel
speaks while dead, Enoch pleases before disappearance, Noah builds against
unseen warning, Abraham goes out without knowing, Sarah judges the promiser
faithful, and the patriarchs die without receiving while still embracing the
promise afar off.

Unseen sat: faith breaks the tyranny of the immediately available country. The
better country, better resurrection, and city with foundations make return to
Egypt, seasonal pleasure, and world-approval look like local optima rather than
truth. The world is not worthy of those it cannot house.

No `sorry`, no new `axiom`.
-/

structure FaithSubstance where
  hopedForHasSubstance : Bool := true
  unseenHasEvidence : Bool := true
  eldersObtainGoodReport : Bool := true
  visibleWorldFramedByUnseenWord : Bool := true
  pleasingGodRequiresFaith : Bool := true
deriving DecidableEq, Repr

def faithSubstance : FaithSubstance := {}

def faithSubstanceWitness (f : FaithSubstance) : Prop :=
  f.hopedForHasSubstance = true ∧
  f.unseenHasEvidence = true ∧
  f.eldersObtainGoodReport = true ∧
  f.visibleWorldFramedByUnseenWord = true ∧
  f.pleasingGodRequiresFaith = true

structure PilgrimPromise where
  abelDeadYetSpeaks : Bool := true
  noahActsOnUnseenWarning : Bool := true
  abrahamGoesOutNotKnowing : Bool := true
  sarahJudgesPromiserFaithful : Bool := true
  strangersSeekBetterCountry : Bool := true
  isaacOfferedUnderResurrectionAccounting : Bool := true
deriving DecidableEq, Repr

def pilgrimPromise : PilgrimPromise := {}

def pilgrimPromiseWitness (p : PilgrimPromise) : Prop :=
  p.abelDeadYetSpeaks = true ∧
  p.noahActsOnUnseenWarning = true ∧
  p.abrahamGoesOutNotKnowing = true ∧
  p.sarahJudgesPromiserFaithful = true ∧
  p.strangersSeekBetterCountry = true ∧
  p.isaacOfferedUnderResurrectionAccounting = true

structure ExodusRefusal where
  mosesRefusesPharaohIdentity : Bool := true
  afflictionChosenOverSeasonalPleasure : Bool := true
  reproachEsteemedGreaterThanEgyptTreasure : Bool := true
  invisibleOneMakesEndurancePossible : Bool := true
  passoverBloodAndRedSeaMarkBoundary : Bool := true
  rahabReceivesPeaceAgainstUnbelief : Bool := true
deriving DecidableEq, Repr

def exodusRefusal : ExodusRefusal := {}

def exodusRefusalWitness (e : ExodusRefusal) : Prop :=
  e.mosesRefusesPharaohIdentity = true ∧
  e.afflictionChosenOverSeasonalPleasure = true ∧
  e.reproachEsteemedGreaterThanEgyptTreasure = true ∧
  e.invisibleOneMakesEndurancePossible = true ∧
  e.passoverBloodAndRedSeaMarkBoundary = true ∧
  e.rahabReceivesPeaceAgainstUnbelief = true

structure WorldUnworthyCounterproof where
  faithWinsWithoutWorldApproval : Bool := true
  faithSuffersWithoutImmediateDeliverance : Bool := true
  betterResurrectionOutranksEscape : Bool := true
  worldCannotHouseItsTruestWitnesses : Bool := true
  promisesAwaitSharedPerfection : Bool := true
deriving DecidableEq, Repr

def worldUnworthyCounterproof : WorldUnworthyCounterproof := {}

def visiblePossessionFinalityRejected (c : WorldUnworthyCounterproof) : Prop :=
  c.faithWinsWithoutWorldApproval = true ∧
  c.faithSuffersWithoutImmediateDeliverance = true ∧
  c.betterResurrectionOutranksEscape = true ∧
  c.worldCannotHouseItsTruestWitnesses = true ∧
  c.promisesAwaitSharedPerfection = true

theorem hebrews_faith_substance :
    faithSubstanceWitness faithSubstance := by
  unfold faithSubstanceWitness faithSubstance
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_pilgrim_promise :
    pilgrimPromiseWitness pilgrimPromise := by
  unfold pilgrimPromiseWitness pilgrimPromise
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_exodus_refusal :
    exodusRefusalWitness exodusRefusal := by
  unfold exodusRefusalWitness exodusRefusal
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_visible_possession_finality_rejected :
    visiblePossessionFinalityRejected worldUnworthyCounterproof := by
  unfold visiblePossessionFinalityRejected worldUnworthyCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_faith_ledger_witness :
    faithSubstanceWitness faithSubstance ∧
    pilgrimPromiseWitness pilgrimPromise ∧
    exodusRefusalWitness exodusRefusal ∧
    visiblePossessionFinalityRejected worldUnworthyCounterproof := by
  exact ⟨hebrews_faith_substance,
    hebrews_pilgrim_promise,
    hebrews_exodus_refusal,
    hebrews_visible_possession_finality_rejected⟩

end HebrewsFaithLedgerWitness
end Gnosis.Witnesses.Bible.Hebrews
