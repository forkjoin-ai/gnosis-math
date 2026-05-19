import Init

namespace Gnosis.Witnesses.Bible.Romans
namespace RomansAllUnderSinWitness

/-!
# Romans 3:9-12 (KJV) -- All Under Sin

This unit gives one bounded universal-sin topology:

  * Jews and Gentiles are already proved all under sin;
  * none is righteous;
  * none understands or seeks after God;
  * all are gone out of the way and become unprofitable;
  * none does good.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- Romans 3:9-12 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def romans_3_9_12_quote : String :=
  "3:9 What then? are we better than they? No, in no wise: for we have " ++
  "before proved both Jews and Gentiles, that they are all under sin; " ++
  "3:10 As it is written, There is none righteous, no, not one: 3:11 " ++
  "There is none that understandeth, there is none that seeketh after " ++
  "God. 3:12 They are all gone out of the way, they are together become " ++
  "unprofitable; there is none that doeth good, no, not one."

/-! ## Section 1: Jew and Gentile under sin -/

/-- The all-under-sin finding in Romans 3:9. -/
structure AllUnderSinFinding where
  notBetterThanThey : Bool
  jewsAndGentilesProved : Bool
  allUnderSin : Bool
deriving DecidableEq, Repr

/-- Romans 3:9 denies superiority and places Jews and Gentiles under sin. -/
def allUnderSinFinding : AllUnderSinFinding where
  notBetterThanThey := true
  jewsAndGentilesProved := true
  allUnderSin := true

/-- The finding is no superiority, both groups, all under sin. -/
theorem all_under_sin_finding_named :
    allUnderSinFinding.notBetterThanThey = true
    ∧ allUnderSinFinding.jewsAndGentilesProved = true
    ∧ allUnderSinFinding.allUnderSin = true := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Section 2: Universal lack -/

/-- The lack-statements in Romans 3:10-12. -/
inductive UniversalLack
  | noneRighteous
  | noneUnderstandeth
  | noneSeekethAfterGod
  | allGoneOutOfWay
  | togetherBecomeUnprofitable
  | noneDoethGood
deriving DecidableEq, Repr

/-- The lack-statements in source order. -/
def universalLacks : List UniversalLack :=
  [ UniversalLack.noneRighteous
  , UniversalLack.noneUnderstandeth
  , UniversalLack.noneSeekethAfterGod
  , UniversalLack.allGoneOutOfWay
  , UniversalLack.togetherBecomeUnprofitable
  , UniversalLack.noneDoethGood
  ]

/-- The chain begins with none righteous. -/
theorem lacks_begin_with_none_righteous :
    universalLacks.head? = some UniversalLack.noneRighteous := rfl

/-- The chain closes with none doing good. -/
theorem lacks_close_with_none_doeth_good :
    universalLacks.getLast? = some UniversalLack.noneDoethGood := rfl

/-! ## Section 3: Master witness -/

/-- The bounded Romans 3:9-12 witness. -/
theorem romans_all_under_sin_witness :
    allUnderSinFinding.notBetterThanThey = true
    ∧ allUnderSinFinding.jewsAndGentilesProved = true
    ∧ allUnderSinFinding.allUnderSin = true
    ∧ universalLacks.length = 6
    ∧ universalLacks.head? = some UniversalLack.noneRighteous
    ∧ universalLacks.getLast? = some UniversalLack.noneDoethGood := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end RomansAllUnderSinWitness
end Gnosis.Witnesses.Bible.Romans
