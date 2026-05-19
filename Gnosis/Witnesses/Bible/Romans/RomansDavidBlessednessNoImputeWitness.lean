import Init

namespace Gnosis.Witnesses.Bible.Romans
namespace RomansDavidBlessednessNoImputeWitness

/-!
# Romans 4:6-8 (KJV) -- David, Blessedness, and No Imputation of Sin

This unit gives one bounded David/blessedness topology:

  * David describes the blessedness of the man to whom God imputes
    righteousness without works;
  * iniquities are forgiven;
  * sins are covered;
  * the Lord will not impute sin.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- Romans 4:6-8 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def romans_4_6_8_quote : String :=
  "4:6 Even as David also describeth the blessedness of the man, unto " ++
  "whom God imputeth righteousness without works, 4:7 Saying, Blessed " ++
  "are they whose iniquities are forgiven, and whose sins are covered. " ++
  "4:8 Blessed is the man to whom the Lord will not impute sin."

/-- The David blessedness pattern in Romans 4:6-8. -/
structure DavidBlessednessPattern where
  davidDescribesBlessedness : Bool
  righteousnessImputedWithoutWorks : Bool
  iniquitiesForgiven : Bool
  sinsCovered : Bool
  lordWillNotImputeSin : Bool
deriving DecidableEq, Repr

/-- David's blessedness witness joins forgiveness, covering, and no imputation. -/
def davidBlessednessPattern : DavidBlessednessPattern where
  davidDescribesBlessedness := true
  righteousnessImputedWithoutWorks := true
  iniquitiesForgiven := true
  sinsCovered := true
  lordWillNotImputeSin := true

/-- The bounded Romans 4:6-8 witness. -/
theorem romans_david_blessedness_no_impute_witness :
    davidBlessednessPattern.davidDescribesBlessedness = true
    ∧ davidBlessednessPattern.righteousnessImputedWithoutWorks = true
    ∧ davidBlessednessPattern.iniquitiesForgiven = true
    ∧ davidBlessednessPattern.sinsCovered = true
    ∧ davidBlessednessPattern.lordWillNotImputeSin = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end RomansDavidBlessednessNoImputeWitness
end Gnosis.Witnesses.Bible.Romans
