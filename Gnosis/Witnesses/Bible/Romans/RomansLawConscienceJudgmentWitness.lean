import Init

namespace Gnosis.Witnesses.Bible.Romans
namespace RomansLawConscienceJudgmentWitness

/-!
# Romans 2:12-16 (KJV) -- Law, Conscience, and Judgment

This unit gives one bounded law/conscience topology:

  * sin without law perishes without law;
  * sin in the law is judged by the law;
  * hearers of the law are not just before God, but doers are justified;
  * Gentiles without the law can do by nature the things contained in the law;
  * their conscience bears witness through accusing or excusing thoughts;
  * the unit closes with God judging secrets by Jesus Christ according to gospel.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- Romans 2:12-16 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def romans_2_12_16_quote : String :=
  "2:12 For as many as have sinned without law shall also perish without " ++
  "law: and as many as have sinned in the law shall be judged by the law; " ++
  "2:13 (For not the hearers of the law are just before God, but the " ++
  "doers of the law shall be justified. 2:14 For when the Gentiles, " ++
  "which have not the law, do by nature the things contained in the law, " ++
  "these, having not the law, are a law unto themselves: 2:15 Which shew " ++
  "the work of the law written in their hearts, their conscience also " ++
  "bearing witness, and their thoughts the mean while accusing or else " ++
  "excusing one another;) 2:16 In the day when God shall judge the " ++
  "secrets of men by Jesus Christ according to my gospel."

/-! ## Section 1: Law-status judgment -/

/-- The law-status outcomes in Romans 2:12. -/
structure LawStatusJudgment where
  sinWithoutLawPerishesWithoutLaw : Bool
  sinInLawJudgedByLaw : Bool
deriving DecidableEq, Repr

/-- Romans 2:12 distinguishes without-law perishing from in-law judgment. -/
def lawStatusJudgment : LawStatusJudgment where
  sinWithoutLawPerishesWithoutLaw := true
  sinInLawJudgedByLaw := true

/-- The two law-status outcomes are both named. -/
theorem law_status_outcomes_named :
    lawStatusJudgment.sinWithoutLawPerishesWithoutLaw = true
    ∧ lawStatusJudgment.sinInLawJudgedByLaw = true := by
  exact ⟨rfl, rfl⟩

/-! ## Section 2: Hearers and doers -/

/-- The hearer/doer contrast in Romans 2:13. -/
structure HearerDoerContrast where
  hearersNotJustBeforeGod : Bool
  doersOfLawJustified : Bool
deriving DecidableEq, Repr

/-- Hearers alone are contrasted with doers of the law. -/
def hearerDoerContrast : HearerDoerContrast where
  hearersNotJustBeforeGod := true
  doersOfLawJustified := true

/-- The doer, not the mere hearer, is the justified side of the contrast. -/
theorem doers_not_hearers_justified :
    hearerDoerContrast.hearersNotJustBeforeGod = true
    ∧ hearerDoerContrast.doersOfLawJustified = true := by
  exact ⟨rfl, rfl⟩

/-! ## Section 3: Gentile conscience witness -/

/-- The Gentile conscience pattern in Romans 2:14-15. -/
structure GentileConsciencePattern where
  gentilesHaveNotLaw : Bool
  doByNatureLawThings : Bool
  lawUntoThemselves : Bool
  workWrittenInHearts : Bool
  conscienceBearingWitness : Bool
  thoughtsAccusingOrExcusing : Bool
deriving DecidableEq, Repr

/-- Gentiles without the law nevertheless show a conscience witness. -/
def gentileConsciencePattern : GentileConsciencePattern where
  gentilesHaveNotLaw := true
  doByNatureLawThings := true
  lawUntoThemselves := true
  workWrittenInHearts := true
  conscienceBearingWitness := true
  thoughtsAccusingOrExcusing := true

/-- Gentiles without the law can do by nature the things contained in the law. -/
theorem gentiles_do_by_nature_law_things :
    gentileConsciencePattern.gentilesHaveNotLaw = true
    ∧ gentileConsciencePattern.doByNatureLawThings = true
    ∧ gentileConsciencePattern.lawUntoThemselves = true := by
  exact ⟨rfl, rfl, rfl⟩

/-- The work written in hearts is accompanied by conscience and thoughts. -/
theorem conscience_bears_accusing_excusing_witness :
    gentileConsciencePattern.workWrittenInHearts = true
    ∧ gentileConsciencePattern.conscienceBearingWitness = true
    ∧ gentileConsciencePattern.thoughtsAccusingOrExcusing = true := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Section 4: Gospel judgment of secrets -/

/-- The closing judgment clause in Romans 2:16. -/
structure GospelSecretsJudgment where
  godJudgesSecretsOfMen : Bool
  byJesusChrist : Bool
  accordingToGospel : Bool
deriving DecidableEq, Repr

/-- God judges the secrets of men by Jesus Christ according to gospel. -/
def gospelSecretsJudgment : GospelSecretsJudgment where
  godJudgesSecretsOfMen := true
  byJesusChrist := true
  accordingToGospel := true

/-- The judgment of secrets is Christ-mediated and gospel-indexed. -/
theorem secrets_judged_by_christ_according_to_gospel :
    gospelSecretsJudgment.godJudgesSecretsOfMen = true
    ∧ gospelSecretsJudgment.byJesusChrist = true
    ∧ gospelSecretsJudgment.accordingToGospel = true := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Section 5: Master witness -/

/-- The bounded Romans 2:12-16 witness. -/
theorem romans_law_conscience_judgment_witness :
    lawStatusJudgment.sinWithoutLawPerishesWithoutLaw = true
    ∧ lawStatusJudgment.sinInLawJudgedByLaw = true
    ∧ hearerDoerContrast.hearersNotJustBeforeGod = true
    ∧ hearerDoerContrast.doersOfLawJustified = true
    ∧ gentileConsciencePattern.gentilesHaveNotLaw = true
    ∧ gentileConsciencePattern.doByNatureLawThings = true
    ∧ gentileConsciencePattern.lawUntoThemselves = true
    ∧ gentileConsciencePattern.workWrittenInHearts = true
    ∧ gentileConsciencePattern.conscienceBearingWitness = true
    ∧ gentileConsciencePattern.thoughtsAccusingOrExcusing = true
    ∧ gospelSecretsJudgment.godJudgesSecretsOfMen = true
    ∧ gospelSecretsJudgment.byJesusChrist = true
    ∧ gospelSecretsJudgment.accordingToGospel = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · rfl
  · rfl
  · rfl

end RomansLawConscienceJudgmentWitness
end Gnosis.Witnesses.Bible.Romans
