import Init

namespace Gnosis.Witnesses.Bible.Romans
namespace RomansUnbeliefFaithTruthWitness

/-!
# Romans 3:3-4 (KJV) -- Unbelief, Faith, and Truth

This unit gives one bounded fidelity topology:

  * some do not believe;
  * their unbelief does not make the faith of God without effect;
  * the answer is "God forbid";
  * God is true though every man is a liar;
  * the citation closes with God's sayings justified and judgment overcome.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- Romans 3:3-4 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def romans_3_3_4_quote : String :=
  "3:3 For what if some did not believe? shall their unbelief make the " ++
  "faith of God without effect? 3:4 God forbid: yea, let God be true, " ++
  "but every man a liar; as it is written, That thou mightest be " ++
  "justified in thy sayings, and mightest overcome when thou art judged."

/-! ## Section 1: Unbelief does not void faith -/

/-- The unbelief/faith question in Romans 3:3. -/
structure UnbeliefFaithQuestion where
  someDidNotBelieve : Bool
  asksWhetherUnbeliefVoidsFaith : Bool
  faithOfGodNotWithoutEffect : Bool
deriving DecidableEq, Repr

/-- Some unbelief does not void the faith of God. -/
def unbeliefFaithQuestion : UnbeliefFaithQuestion where
  someDidNotBelieve := true
  asksWhetherUnbeliefVoidsFaith := true
  faithOfGodNotWithoutEffect := true

/-- The witness preserves both the question and its negative answer. -/
theorem unbelief_does_not_void_faith :
    unbeliefFaithQuestion.someDidNotBelieve = true
    ∧ unbeliefFaithQuestion.asksWhetherUnbeliefVoidsFaith = true
    ∧ unbeliefFaithQuestion.faithOfGodNotWithoutEffect = true := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Section 2: God true, man liar -/

/-- The God-forbid truth contrast in Romans 3:4. -/
structure TruthContrast where
  godForbid : Bool
  godTrue : Bool
  everyManLiar : Bool
deriving DecidableEq, Repr

/-- God remains true though every man is a liar. -/
def truthContrast : TruthContrast where
  godForbid := true
  godTrue := true
  everyManLiar := true

/-- The answer negates the implication and states the truth contrast. -/
theorem god_true_every_man_liar :
    truthContrast.godForbid = true
    ∧ truthContrast.godTrue = true
    ∧ truthContrast.everyManLiar = true := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Section 3: Citation closure -/

/-- The citation closure in Romans 3:4. -/
structure CitationVindication where
  justifiedInSayings : Bool
  overcomeWhenJudged : Bool
deriving DecidableEq, Repr

/-- The citation names justification in sayings and overcoming in judgment. -/
def citationVindication : CitationVindication where
  justifiedInSayings := true
  overcomeWhenJudged := true

/-- God's sayings are justified and God overcomes when judged. -/
theorem sayings_justified_overcome_judged :
    citationVindication.justifiedInSayings = true
    ∧ citationVindication.overcomeWhenJudged = true := by
  exact ⟨rfl, rfl⟩

/-! ## Section 4: Master witness -/

/-- The bounded Romans 3:3-4 witness. -/
theorem romans_unbelief_faith_truth_witness :
    unbeliefFaithQuestion.someDidNotBelieve = true
    ∧ unbeliefFaithQuestion.asksWhetherUnbeliefVoidsFaith = true
    ∧ unbeliefFaithQuestion.faithOfGodNotWithoutEffect = true
    ∧ truthContrast.godForbid = true
    ∧ truthContrast.godTrue = true
    ∧ truthContrast.everyManLiar = true
    ∧ citationVindication.justifiedInSayings = true
    ∧ citationVindication.overcomeWhenJudged = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end RomansUnbeliefFaithTruthWitness
end Gnosis.Witnesses.Bible.Romans
