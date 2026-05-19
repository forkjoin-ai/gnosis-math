import Init

namespace Gnosis.Witnesses.Bible.Romans
namespace RomansUnrighteousnessJudgmentSlanderWitness

/-!
# Romans 3:5-8 (KJV) -- Unrighteousness, Judgment, and Slander

This unit gives one bounded objection topology:

  * the objection asks whether unrighteousness commends God's righteousness;
  * the answer rejects that God is unrighteous in taking vengeance;
  * otherwise, God could not judge the world;
  * the lie/truth objection does not remove judgment as sinner;
  * the slanderous "let us do evil, that good may come" report is condemned.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- Romans 3:5-8 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def romans_3_5_8_quote : String :=
  "3:5 But if our unrighteousness commend the righteousness of God, " ++
  "what shall we say? Is God unrighteous who taketh vengeance? (I speak " ++
  "as a man) 3:6 God forbid: for then how shall God judge the world? " ++
  "3:7 For if the truth of God hath more abounded through my lie unto " ++
  "his glory; why yet am I also judged as a sinner? 3:8 And not rather, " ++
  "(as we be slanderously reported, and as some affirm that we say,) " ++
  "Let us do evil, that good may come? whose damnation is just."

/-! ## Section 1: Righteousness objection -/

/-- The unrighteousness/righteousness objection in Romans 3:5. -/
structure RighteousnessObjection where
  unrighteousnessCommendsRighteousnessQuestion : Bool
  asksIfGodUnrighteousTakingVengeance : Bool
  speaksAsMan : Bool
deriving DecidableEq, Repr

/-- The objection is raised as a human-speaking question. -/
def righteousnessObjection : RighteousnessObjection where
  unrighteousnessCommendsRighteousnessQuestion := true
  asksIfGodUnrighteousTakingVengeance := true
  speaksAsMan := true

/-- The objection binds human speech to the vengeance question. -/
theorem righteousness_objection_named :
    righteousnessObjection.unrighteousnessCommendsRighteousnessQuestion = true
    ∧ righteousnessObjection.asksIfGodUnrighteousTakingVengeance = true
    ∧ righteousnessObjection.speaksAsMan = true := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Section 2: Judgment answer -/

/-- The judgment answer in Romans 3:6-7. -/
structure JudgmentAnswer where
  godForbid : Bool
  godJudgesWorld : Bool
  truthAboundsThroughLieQuestion : Bool
  stillJudgedAsSinner : Bool
deriving DecidableEq, Repr

/-- The answer preserves world judgment and sinner judgment. -/
def judgmentAnswer : JudgmentAnswer where
  godForbid := true
  godJudgesWorld := true
  truthAboundsThroughLieQuestion := true
  stillJudgedAsSinner := true

/-- God forbid: God remains judge of the world. -/
theorem god_remains_world_judge :
    judgmentAnswer.godForbid = true
    ∧ judgmentAnswer.godJudgesWorld = true := by
  exact ⟨rfl, rfl⟩

/-- The lie/truth objection does not remove being judged as sinner. -/
theorem lie_truth_objection_still_judged :
    judgmentAnswer.truthAboundsThroughLieQuestion = true
    ∧ judgmentAnswer.stillJudgedAsSinner = true := by
  exact ⟨rfl, rfl⟩

/-! ## Section 3: Slanderous evil-for-good report -/

/-- The slander and condemnation clause in Romans 3:8. -/
structure SlanderCondemnation where
  slanderouslyReported : Bool
  letUsDoEvilThatGoodMayCome : Bool
  damnationIsJust : Bool
deriving DecidableEq, Repr

/-- The slanderous "do evil that good may come" report is justly condemned. -/
def slanderCondemnation : SlanderCondemnation where
  slanderouslyReported := true
  letUsDoEvilThatGoodMayCome := true
  damnationIsJust := true

/-- The evil-for-good slander receives just damnation. -/
theorem evil_for_good_slander_condemned :
    slanderCondemnation.slanderouslyReported = true
    ∧ slanderCondemnation.letUsDoEvilThatGoodMayCome = true
    ∧ slanderCondemnation.damnationIsJust = true := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Section 4: Master witness -/

/-- The bounded Romans 3:5-8 witness. -/
theorem romans_unrighteousness_judgment_slander_witness :
    righteousnessObjection.unrighteousnessCommendsRighteousnessQuestion = true
    ∧ righteousnessObjection.asksIfGodUnrighteousTakingVengeance = true
    ∧ righteousnessObjection.speaksAsMan = true
    ∧ judgmentAnswer.godForbid = true
    ∧ judgmentAnswer.godJudgesWorld = true
    ∧ judgmentAnswer.truthAboundsThroughLieQuestion = true
    ∧ judgmentAnswer.stillJudgedAsSinner = true
    ∧ slanderCondemnation.slanderouslyReported = true
    ∧ slanderCondemnation.letUsDoEvilThatGoodMayCome = true
    ∧ slanderCondemnation.damnationIsJust = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end RomansUnrighteousnessJudgmentSlanderWitness
end Gnosis.Witnesses.Bible.Romans
