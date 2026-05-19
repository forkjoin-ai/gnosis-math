import Init

namespace Gnosis.Witnesses.Bible.Romans
namespace RomansAbrahamUncircumcisedFaithSealWitness

/-!
# Romans 4:9-12 (KJV) -- Abraham, Uncircumcision, and Faith's Seal

This unit gives one bounded reckoning/seal topology:

  * blessedness extends to uncircumcision as well as circumcision;
  * Abraham's faith was reckoned for righteousness while uncircumcised;
  * circumcision is received as a sign and seal;
  * Abraham becomes father of believing uncircumcision and faithful circumcision.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- Romans 4:9-12 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def romans_4_9_12_quote : String :=
  "4:9 Cometh this blessedness then upon the circumcision only, or upon " ++
  "the uncircumcision also? for we say that faith was reckoned to " ++
  "Abraham for righteousness. 4:10 How was it then reckoned? when he " ++
  "was in circumcision, or in uncircumcision? Not in circumcision, but " ++
  "in uncircumcision. 4:11 And he received the sign of circumcision, a " ++
  "seal of the righteousness of the faith which he had yet being " ++
  "uncircumcised: that he might be the father of all them that believe, " ++
  "though they be not circumcised; that righteousness might be imputed " ++
  "unto them also: 4:12 And the father of circumcision to them who are " ++
  "not of the circumcision only, but who also walk in the steps of that " ++
  "faith of our father Abraham, which he had being yet uncircumcised."

/-- The timing of Abraham's reckoned faith in Romans 4:9-10. -/
structure AbrahamReckoningTiming where
  blessednessAlsoUponUncircumcision : Bool
  faithReckonedForRighteousness : Bool
  notInCircumcision : Bool
  inUncircumcision : Bool
deriving DecidableEq, Repr

/-- Abraham's faith is reckoned in uncircumcision. -/
def abrahamReckoningTiming : AbrahamReckoningTiming where
  blessednessAlsoUponUncircumcision := true
  faithReckonedForRighteousness := true
  notInCircumcision := true
  inUncircumcision := true

/-- The sign/seal and fatherhood pattern in Romans 4:11-12. -/
structure FaithSealFatherhood where
  signOfCircumcision : Bool
  sealOfRighteousnessOfFaith : Bool
  fatherOfUncircumcisedBelievers : Bool
  righteousnessImputedToThemAlso : Bool
  fatherOfCircumcisionWalkingInFaithSteps : Bool
deriving DecidableEq, Repr

/-- Circumcision seals prior faith and Abraham fathers believing groups. -/
def faithSealFatherhood : FaithSealFatherhood where
  signOfCircumcision := true
  sealOfRighteousnessOfFaith := true
  fatherOfUncircumcisedBelievers := true
  righteousnessImputedToThemAlso := true
  fatherOfCircumcisionWalkingInFaithSteps := true

/-- The bounded Romans 4:9-12 witness. -/
theorem romans_abraham_uncircumcised_faith_seal_witness :
    abrahamReckoningTiming.blessednessAlsoUponUncircumcision = true
    ∧ abrahamReckoningTiming.faithReckonedForRighteousness = true
    ∧ abrahamReckoningTiming.notInCircumcision = true
    ∧ abrahamReckoningTiming.inUncircumcision = true
    ∧ faithSealFatherhood.signOfCircumcision = true
    ∧ faithSealFatherhood.sealOfRighteousnessOfFaith = true
    ∧ faithSealFatherhood.fatherOfUncircumcisedBelievers = true
    ∧ faithSealFatherhood.righteousnessImputedToThemAlso = true
    ∧ faithSealFatherhood.fatherOfCircumcisionWalkingInFaithSteps = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end RomansAbrahamUncircumcisedFaithSealWitness
end Gnosis.Witnesses.Bible.Romans
