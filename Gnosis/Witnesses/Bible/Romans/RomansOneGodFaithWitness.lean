import Init

namespace Gnosis.Witnesses.Bible.Romans
namespace RomansOneGodFaithWitness

/-!
# Romans 3:29-30 (KJV) -- One God, Jew and Gentile

This unit gives one bounded one-God topology:

  * God is not God of Jews only, but of Gentiles also;
  * one God justifies circumcision by faith;
  * the same God justifies uncircumcision through faith.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- Romans 3:29-30 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def romans_3_29_30_quote : String :=
  "3:29 Is he the God of the Jews only? is he not also of the Gentiles? " ++
  "Yes, of the Gentiles also: 3:30 Seeing it is one God, which shall " ++
  "justify the circumcision by faith, and uncircumcision through faith."

/-- The Jew/Gentile one-God pattern in Romans 3:29-30. -/
structure OneGodFaithPattern where
  notJewsOnly : Bool
  gentilesAlso : Bool
  oneGod : Bool
  circumcisionJustifiedByFaith : Bool
  uncircumcisionJustifiedThroughFaith : Bool
deriving DecidableEq, Repr

/-- The one God justifies circumcision and uncircumcision by/through faith. -/
def oneGodFaithPattern : OneGodFaithPattern where
  notJewsOnly := true
  gentilesAlso := true
  oneGod := true
  circumcisionJustifiedByFaith := true
  uncircumcisionJustifiedThroughFaith := true

/-- The bounded Romans 3:29-30 witness. -/
theorem romans_one_god_faith_witness :
    oneGodFaithPattern.notJewsOnly = true
    ∧ oneGodFaithPattern.gentilesAlso = true
    ∧ oneGodFaithPattern.oneGod = true
    ∧ oneGodFaithPattern.circumcisionJustifiedByFaith = true
    ∧ oneGodFaithPattern.uncircumcisionJustifiedThroughFaith = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end RomansOneGodFaithWitness
end Gnosis.Witnesses.Bible.Romans
