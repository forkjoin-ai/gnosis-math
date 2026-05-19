import Init

namespace Gnosis.Witnesses.Bible.Romans
namespace RomansAbrahamBelievedCountedWitness

/-!
# Romans 4:1-5 (KJV) -- Abraham Believed and It Was Counted

This unit gives one bounded Abraham/faith topology:

  * Abraham has no glory before God if justified by works;
  * scripture says Abraham believed God;
  * belief was counted unto him for righteousness;
  * reward to the worker is debt, not grace;
  * faith is counted for righteousness to the one who believes on the justifier
    of the ungodly.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- Romans 4:1-5 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def romans_4_1_5_quote : String :=
  "4:1 What shall we say then that Abraham our father, as pertaining to " ++
  "the flesh, hath found? 4:2 For if Abraham were justified by works, he " ++
  "hath whereof to glory; but not before God. 4:3 For what saith the " ++
  "scripture? Abraham believed God, and it was counted unto him for " ++
  "righteousness. 4:4 Now to him that worketh is the reward not reckoned " ++
  "of grace, but of debt. 4:5 But to him that worketh not, but believeth " ++
  "on him that justifieth the ungodly, his faith is counted for " ++
  "righteousness."

/-- The Abraham works/boasting contrast in Romans 4:1-2. -/
structure AbrahamWorksContrast where
  abrahamFatherPertainingToFleshQuestion : Bool
  justifiedByWorksWouldGlory : Bool
  notBeforeGod : Bool
deriving DecidableEq, Repr

/-- Abraham's works do not ground glory before God. -/
def abrahamWorksContrast : AbrahamWorksContrast where
  abrahamFatherPertainingToFleshQuestion := true
  justifiedByWorksWouldGlory := true
  notBeforeGod := true

/-- The scripture citation and counting pattern in Romans 4:3-5. -/
structure FaithCountedPattern where
  scriptureSaysAbrahamBelievedGod : Bool
  countedForRighteousness : Bool
  workerRewardDebtNotGrace : Bool
  nonWorkerBelievesJustifierUngodly : Bool
  faithCountedForRighteousness : Bool
deriving DecidableEq, Repr

/-- Belief, not working, is counted for righteousness. -/
def faithCountedPattern : FaithCountedPattern where
  scriptureSaysAbrahamBelievedGod := true
  countedForRighteousness := true
  workerRewardDebtNotGrace := true
  nonWorkerBelievesJustifierUngodly := true
  faithCountedForRighteousness := true

/-- The bounded Romans 4:1-5 witness. -/
theorem romans_abraham_believed_counted_witness :
    abrahamWorksContrast.abrahamFatherPertainingToFleshQuestion = true
    ∧ abrahamWorksContrast.justifiedByWorksWouldGlory = true
    ∧ abrahamWorksContrast.notBeforeGod = true
    ∧ faithCountedPattern.scriptureSaysAbrahamBelievedGod = true
    ∧ faithCountedPattern.countedForRighteousness = true
    ∧ faithCountedPattern.workerRewardDebtNotGrace = true
    ∧ faithCountedPattern.nonWorkerBelievesJustifierUngodly = true
    ∧ faithCountedPattern.faithCountedForRighteousness = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end RomansAbrahamBelievedCountedWitness
end Gnosis.Witnesses.Bible.Romans
