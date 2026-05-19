import Init

namespace Gnosis.Witnesses.Bible.Romans
namespace RomansJewAdvantageOraclesWitness

/-!
# Romans 3:1-2 (KJV) -- Advantage and Oracles

This unit gives one bounded advantage topology:

  * the question asks what advantage the Jew has and what profit circumcision has;
  * the answer says much every way;
  * chiefly, the oracles of God were committed unto them.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- Romans 3:1-2 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def romans_3_1_2_quote : String :=
  "3:1 What advantage then hath the Jew? or what profit is there of " ++
  "circumcision? 3:2 Much every way: chiefly, because that unto them " ++
  "were committed the oracles of God."

/-! ## Section 1: Question and answer -/

/-- The advantage/profit question in Romans 3:1. -/
structure AdvantageQuestion where
  asksJewAdvantage : Bool
  asksCircumcisionProfit : Bool
deriving DecidableEq, Repr

/-- Romans 3:1 asks both advantage and profit questions. -/
def advantageQuestion : AdvantageQuestion where
  asksJewAdvantage := true
  asksCircumcisionProfit := true

/-- The question has both Jew-advantage and circumcision-profit parts. -/
theorem advantage_question_has_two_parts :
    advantageQuestion.asksJewAdvantage = true
    ∧ advantageQuestion.asksCircumcisionProfit = true := by
  exact ⟨rfl, rfl⟩

/-- The answer in Romans 3:2. -/
structure OraclesAnswer where
  muchEveryWay : Bool
  chieflyOraclesCommitted : Bool
  oraclesOfGod : Bool
deriving DecidableEq, Repr

/-- The stated chief advantage is that the oracles of God were committed. -/
def oraclesAnswer : OraclesAnswer where
  muchEveryWay := true
  chieflyOraclesCommitted := true
  oraclesOfGod := true

/-- The answer is much every way, chiefly the committed oracles of God. -/
theorem chief_advantage_is_oracles :
    oraclesAnswer.muchEveryWay = true
    ∧ oraclesAnswer.chieflyOraclesCommitted = true
    ∧ oraclesAnswer.oraclesOfGod = true := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Section 2: Master witness -/

/-- The bounded Romans 3:1-2 witness. -/
theorem romans_jew_advantage_oracles_witness :
    advantageQuestion.asksJewAdvantage = true
    ∧ advantageQuestion.asksCircumcisionProfit = true
    ∧ oraclesAnswer.muchEveryWay = true
    ∧ oraclesAnswer.chieflyOraclesCommitted = true
    ∧ oraclesAnswer.oraclesOfGod = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end RomansJewAdvantageOraclesWitness
end Gnosis.Witnesses.Bible.Romans
