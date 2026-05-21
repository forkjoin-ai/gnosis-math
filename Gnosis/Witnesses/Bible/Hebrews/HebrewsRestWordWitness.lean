namespace Gnosis.Witnesses.Bible.Hebrews
namespace HebrewsRestWordWitness

/-!
# Hebrews 4 -- Remaining Rest, Exposing Word, and Bold Access

Source slice: Hebrews 4:1-16.

Chapter invariant: rest remains open, but only as heard word mixed with faith.
The wilderness failure does not close the promise; it exposes the gap between
receiving proclamation and entering by belief.

Primary gap/counterproof: sacred history, Sabbath memory, and Joshua's entry do
not exhaust rest. If another Today is still spoken, then rest is not reducible to
past land-entry or past ritual time; the promise remains as a live aperture that
can still be missed through unbelief.

Unseen sat: the word that opens rest also exposes the hearer. It cuts through
soul/spirit and joint/marrow, making all creatures naked before God; only then
does the great high priest turn exposure into bold access to mercy and timely
grace.

No `sorry`, no new `axiom`.
-/

structure RemainingRest where
  promiseRemainsOpen : Bool := true
  preachedWordMustMixWithFaith : Bool := true
  believersEnterRest : Bool := true
  anotherTodayLimitsTheDay : Bool := true
  sabbathRestRemains : Bool := true
deriving DecidableEq, Repr

def remainingRest : RemainingRest := {}

def remainingRestWitness (r : RemainingRest) : Prop :=
  r.promiseRemainsOpen = true ∧
  r.preachedWordMustMixWithFaith = true ∧
  r.believersEnterRest = true ∧
  r.anotherTodayLimitsTheDay = true ∧
  r.sabbathRestRemains = true

structure RestCounterproof where
  joshuaEntryDoesNotExhaustRest : Bool := true
  pastSabbathDoesNotCloseRest : Bool := true
  unbeliefCanStillComeShort : Bool := true
  labourAimsAtEnteringRest : Bool := true
deriving DecidableEq, Repr

def restCounterproof : RestCounterproof := {}

def prematureRestClosureRejected (c : RestCounterproof) : Prop :=
  c.joshuaEntryDoesNotExhaustRest = true ∧
  c.pastSabbathDoesNotCloseRest = true ∧
  c.unbeliefCanStillComeShort = true ∧
  c.labourAimsAtEnteringRest = true

structure WordAndPriestAccess where
  wordIsLivingAndPowerful : Bool := true
  wordDividesAndDiscerns : Bool := true
  creaturesManifestBeforeGod : Bool := true
  greatHighPriestPassedHeavens : Bool := true
  temptedWithoutSinGivesBoldAccess : Bool := true
deriving DecidableEq, Repr

def wordAndPriestAccess : WordAndPriestAccess := {}

def exposureMercyWitness (a : WordAndPriestAccess) : Prop :=
  a.wordIsLivingAndPowerful = true ∧
  a.wordDividesAndDiscerns = true ∧
  a.creaturesManifestBeforeGod = true ∧
  a.greatHighPriestPassedHeavens = true ∧
  a.temptedWithoutSinGivesBoldAccess = true

theorem hebrews_remaining_rest :
    remainingRestWitness remainingRest := by
  unfold remainingRestWitness remainingRest
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_premature_rest_closure_rejected :
    prematureRestClosureRejected restCounterproof := by
  unfold prematureRestClosureRejected restCounterproof
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem hebrews_exposure_mercy :
    exposureMercyWitness wordAndPriestAccess := by
  unfold exposureMercyWitness wordAndPriestAccess
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_rest_word_witness :
    remainingRestWitness remainingRest ∧
    prematureRestClosureRejected restCounterproof ∧
    exposureMercyWitness wordAndPriestAccess := by
  exact ⟨hebrews_remaining_rest,
    hebrews_premature_rest_closure_rejected,
    hebrews_exposure_mercy⟩

end HebrewsRestWordWitness
end Gnosis.Witnesses.Bible.Hebrews
