import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansPromiseBeforeLawWitness

/-!
# Galatians 3:15-18 -- Confirmed Promise Before Later Law

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93751-93763`.

Paul's timing argument is a namespace-priority claim: a confirmed promise cannot
be disannulled by a later law layer. The inheritance therefore remains promise
indexed, not law indexed.

No `sorry`, no new `axiom`.
-/

structure ConfirmedCovenantPriority where
  humanCovenantAnalogyNamed : Bool := true
  confirmedCovenantNotDisannulled : Bool := true
  nothingAddedAfterConfirmation : Bool := true
  promisesMadeToAbrahamAndSeed : Bool := true
  singularSeedReadAsChrist : Bool := true
deriving DecidableEq, Repr

def confirmedCovenantPriority : ConfirmedCovenantPriority := {}

def promisePriorityWitness (p : ConfirmedCovenantPriority) : Prop :=
  p.humanCovenantAnalogyNamed = true ∧
  p.confirmedCovenantNotDisannulled = true ∧
  p.nothingAddedAfterConfirmation = true ∧
  p.promisesMadeToAbrahamAndSeed = true ∧
  p.singularSeedReadAsChrist = true

structure LawAfterPromise where
  lawFourHundredThirtyYearsAfter : Bool := true
  laterLawCannotDisannul : Bool := true
  promiseCannotBeMadeVoid : Bool := true
  inheritanceNotOfLaw : Bool := true
  inheritanceGivenByPromise : Bool := true
deriving DecidableEq, Repr

def lawAfterPromise : LawAfterPromise := {}

def inheritanceByPromiseNotLaw (l : LawAfterPromise) : Prop :=
  l.lawFourHundredThirtyYearsAfter = true ∧
  l.laterLawCannotDisannul = true ∧
  l.promiseCannotBeMadeVoid = true ∧
  l.inheritanceNotOfLaw = true ∧
  l.inheritanceGivenByPromise = true

theorem galatians_promise_priority :
    promisePriorityWitness confirmedCovenantPriority := by
  unfold promisePriorityWitness confirmedCovenantPriority
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_inheritance_by_promise_not_law :
    inheritanceByPromiseNotLaw lawAfterPromise := by
  unfold inheritanceByPromiseNotLaw lawAfterPromise
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_promise_before_law_witness :
    promisePriorityWitness confirmedCovenantPriority ∧
    inheritanceByPromiseNotLaw lawAfterPromise := by
  exact ⟨galatians_promise_priority,
    galatians_inheritance_by_promise_not_law⟩

end GalatiansPromiseBeforeLawWitness
end Gnosis.Witnesses.Bible.Galatians
