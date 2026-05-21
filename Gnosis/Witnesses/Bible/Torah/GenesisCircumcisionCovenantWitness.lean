import Init

namespace Gnosis.Witnesses.Bible.Torah
namespace GenesisCircumcisionCovenantWitness

/-!
# Genesis 17:2-14 -- Abraham, Covenant, and Circumcision Token

Source text: `docs/ebooks/source-texts/bible-kjv.txt:1255-1295`.

This Torah anchor records circumcision as covenant token, not as a duplicate of
later Pauline dispute text. The overlap with Galatians is semantic: covenant
sign versus gospel-capture mechanism.

No `sorry`, no new `axiom`.
-/

structure AbrahamCovenantPromise where
  covenantMadeWithAbram : Bool := true
  fatherOfManyNations : Bool := true
  abramRenamedAbraham : Bool := true
  nationsAndKingsPromised : Bool := true
  everlastingCovenantEstablished : Bool := true
  landAndGodRelationPromised : Bool := true
deriving DecidableEq, Repr

def abrahamCovenantPromise : AbrahamCovenantPromise := {}

def abrahamCovenantPromiseWitness (p : AbrahamCovenantPromise) : Prop :=
  p.covenantMadeWithAbram = true ∧
  p.fatherOfManyNations = true ∧
  p.abramRenamedAbraham = true ∧
  p.nationsAndKingsPromised = true ∧
  p.everlastingCovenantEstablished = true ∧
  p.landAndGodRelationPromised = true

structure CircumcisionToken where
  covenantKeptBySeedGenerations : Bool := true
  everyMaleChildCircumcised : Bool := true
  foreskinCircumcisionToken : Bool := true
  eighthDayNamed : Bool := true
  householdAndBoughtStrangerIncluded : Bool := true
  covenantInFleshEverlasting : Bool := true
  uncircumcisedMaleBreaksCovenant : Bool := true
deriving DecidableEq, Repr

def circumcisionToken : CircumcisionToken := {}

def circumcisionIsCovenantToken (t : CircumcisionToken) : Prop :=
  t.covenantKeptBySeedGenerations = true ∧
  t.everyMaleChildCircumcised = true ∧
  t.foreskinCircumcisionToken = true ∧
  t.eighthDayNamed = true ∧
  t.householdAndBoughtStrangerIncluded = true ∧
  t.covenantInFleshEverlasting = true ∧
  t.uncircumcisedMaleBreaksCovenant = true

theorem genesis_abraham_covenant_promise :
    abrahamCovenantPromiseWitness abrahamCovenantPromise := by
  unfold abrahamCovenantPromiseWitness abrahamCovenantPromise
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem genesis_circumcision_token :
    circumcisionIsCovenantToken circumcisionToken := by
  unfold circumcisionIsCovenantToken circumcisionToken
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem genesis_circumcision_covenant_witness :
    abrahamCovenantPromiseWitness abrahamCovenantPromise ∧
    circumcisionIsCovenantToken circumcisionToken := by
  exact ⟨genesis_abraham_covenant_promise, genesis_circumcision_token⟩

end GenesisCircumcisionCovenantWitness
end Gnosis.Witnesses.Bible.Torah
