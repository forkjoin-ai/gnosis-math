import Init

namespace Gnosis.Witnesses.Bible.Romans
namespace RomansCircumcisionHeartSpiritWitness

/-!
# Romans 2:25-29 (KJV) -- Circumcision, Heart, and Spirit

This unit gives one bounded circumcision topology:

  * circumcision profits if the law is kept;
  * law-breaking makes circumcision uncircumcision;
  * uncircumcision keeping the law is counted for circumcision;
  * outward Jewishness and fleshly circumcision are displaced;
  * inward Jewishness and heart-circumcision in spirit receive praise from God.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- Romans 2:25-29 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def romans_2_25_29_quote : String :=
  "2:25 For circumcision verily profiteth, if thou keep the law: but " ++
  "if thou be a breaker of the law, thy circumcision is made " ++
  "uncircumcision. 2:26 Therefore if the uncircumcision keep the " ++
  "righteousness of the law, shall not his uncircumcision be counted " ++
  "for circumcision? 2:27 And shall not uncircumcision which is by " ++
  "nature, if it fulfil the law, judge thee, who by the letter and " ++
  "circumcision dost transgress the law? 2:28 For he is not a Jew, " ++
  "which is one outwardly; neither is that circumcision, which is " ++
  "outward in the flesh: 2:29 But he is a Jew, which is one inwardly; " ++
  "and circumcision is that of the heart, in the spirit, and not in " ++
  "the letter; whose praise is not of men, but of God."

/-! ## Section 1: Conditional circumcision -/

/-- The circumcision/law conditional in Romans 2:25. -/
structure CircumcisionLawConditional where
  circumcisionProfitsIfLawKept : Bool
  lawBreakerCircumcisionMadeUncircumcision : Bool
deriving DecidableEq, Repr

/-- Circumcision is profitably tied to law-keeping, and undone by law-breaking. -/
def circumcisionLawConditional : CircumcisionLawConditional where
  circumcisionProfitsIfLawKept := true
  lawBreakerCircumcisionMadeUncircumcision := true

/-- Romans 2:25 names the law-keeping and law-breaking conditions. -/
theorem circumcision_condition_named :
    circumcisionLawConditional.circumcisionProfitsIfLawKept = true
    ∧ circumcisionLawConditional.lawBreakerCircumcisionMadeUncircumcision = true := by
  exact ⟨rfl, rfl⟩

/-! ## Section 2: Uncircumcision keeping law -/

/-- The uncircumcision law-keeping pattern in Romans 2:26-27. -/
structure UncircumcisionLawKeeping where
  uncircumcisionKeepsRighteousnessOfLaw : Bool
  countedForCircumcision : Bool
  naturalUncircumcisionFulfilsLaw : Bool
  judgesLetterCircumcisionTransgressor : Bool
deriving DecidableEq, Repr

/-- Law-keeping uncircumcision is counted for circumcision and judges transgression. -/
def uncircumcisionLawKeeping : UncircumcisionLawKeeping where
  uncircumcisionKeepsRighteousnessOfLaw := true
  countedForCircumcision := true
  naturalUncircumcisionFulfilsLaw := true
  judgesLetterCircumcisionTransgressor := true

/-- Uncircumcision keeping law is counted for circumcision. -/
theorem uncircumcision_counted_for_circumcision :
    uncircumcisionLawKeeping.uncircumcisionKeepsRighteousnessOfLaw = true
    ∧ uncircumcisionLawKeeping.countedForCircumcision = true := by
  exact ⟨rfl, rfl⟩

/-- Natural uncircumcision fulfilling law judges the transgressor by letter and circumcision. -/
theorem natural_uncircumcision_judges_transgressor :
    uncircumcisionLawKeeping.naturalUncircumcisionFulfilsLaw = true
    ∧ uncircumcisionLawKeeping.judgesLetterCircumcisionTransgressor = true := by
  exact ⟨rfl, rfl⟩

/-! ## Section 3: Outward and inward distinction -/

/-- The outward/inward distinction in Romans 2:28-29. -/
structure InwardJewPattern where
  notOutwardJew : Bool
  notOutwardFleshCircumcision : Bool
  inwardJew : Bool
  circumcisionOfHeart : Bool
  inSpiritNotLetter : Bool
  praiseOfGodNotMen : Bool
deriving DecidableEq, Repr

/-- True Jewishness and circumcision are located inwardly, in heart and spirit. -/
def inwardJewPattern : InwardJewPattern where
  notOutwardJew := true
  notOutwardFleshCircumcision := true
  inwardJew := true
  circumcisionOfHeart := true
  inSpiritNotLetter := true
  praiseOfGodNotMen := true

/-- Outward Jewishness and fleshly circumcision are negated. -/
theorem not_outward_jew_or_flesh_circumcision :
    inwardJewPattern.notOutwardJew = true
    ∧ inwardJewPattern.notOutwardFleshCircumcision = true := by
  exact ⟨rfl, rfl⟩

/-- Inward Jewishness is heart-circumcision in spirit, praised by God. -/
theorem inward_heart_spirit_praise_of_god :
    inwardJewPattern.inwardJew = true
    ∧ inwardJewPattern.circumcisionOfHeart = true
    ∧ inwardJewPattern.inSpiritNotLetter = true
    ∧ inwardJewPattern.praiseOfGodNotMen = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Section 4: Master witness -/

/-- The bounded Romans 2:25-29 witness. -/
theorem romans_circumcision_heart_spirit_witness :
    circumcisionLawConditional.circumcisionProfitsIfLawKept = true
    ∧ circumcisionLawConditional.lawBreakerCircumcisionMadeUncircumcision = true
    ∧ uncircumcisionLawKeeping.uncircumcisionKeepsRighteousnessOfLaw = true
    ∧ uncircumcisionLawKeeping.countedForCircumcision = true
    ∧ uncircumcisionLawKeeping.naturalUncircumcisionFulfilsLaw = true
    ∧ uncircumcisionLawKeeping.judgesLetterCircumcisionTransgressor = true
    ∧ inwardJewPattern.notOutwardJew = true
    ∧ inwardJewPattern.notOutwardFleshCircumcision = true
    ∧ inwardJewPattern.inwardJew = true
    ∧ inwardJewPattern.circumcisionOfHeart = true
    ∧ inwardJewPattern.inSpiritNotLetter = true
    ∧ inwardJewPattern.praiseOfGodNotMen = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

end RomansCircumcisionHeartSpiritWitness
end Gnosis.Witnesses.Bible.Romans
