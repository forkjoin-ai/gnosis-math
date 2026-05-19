import Init

namespace Gnosis.Witnesses.Bible.Romans
namespace RomansRighteousnessFaithPropitiationWitness

/-!
# Romans 3:21-26 (KJV) -- Righteousness, Faith, and Propitiation

This unit gives one bounded righteousness-by-faith topology:

  * righteousness of God without the law is manifested;
  * it is witnessed by the law and prophets;
  * it is by faith of Jesus Christ unto and upon all who believe;
  * all have sinned and come short of God's glory;
  * justification is free by grace through redemption in Christ Jesus;
  * Christ is set forth as propitiation through faith in his blood;
  * God is just and the justifier of the believer in Jesus.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- Romans 3:21-26 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def romans_3_21_26_quote : String :=
  "3:21 But now the righteousness of God without the law is manifested, " ++
  "being witnessed by the law and the prophets; 3:22 Even the " ++
  "righteousness of God which is by faith of Jesus Christ unto all and " ++
  "upon all them that believe: for there is no difference: 3:23 For all " ++
  "have sinned, and come short of the glory of God; 3:24 Being justified " ++
  "freely by his grace through the redemption that is in Christ Jesus: " ++
  "3:25 Whom God hath set forth to be a propitiation through faith in " ++
  "his blood, to declare his righteousness for the remission of sins that " ++
  "are past, through the forbearance of God; 3:26 To declare, I say, at " ++
  "this time his righteousness: that he might be just, and the justifier " ++
  "of him which believeth in Jesus."

/-! ## Section 1: Manifest righteousness -/

/-- The manifestation pattern in Romans 3:21-22. -/
structure ManifestRighteousness where
  righteousnessWithoutLawManifested : Bool
  witnessedByLawAndProphets : Bool
  byFaithOfJesusChrist : Bool
  untoAllAndUponBelievers : Bool
  noDifference : Bool
deriving DecidableEq, Repr

/-- The righteousness of God is manifested apart from law and witnessed by law and prophets. -/
def manifestRighteousness : ManifestRighteousness where
  righteousnessWithoutLawManifested := true
  witnessedByLawAndProphets := true
  byFaithOfJesusChrist := true
  untoAllAndUponBelievers := true
  noDifference := true

/-- Manifest righteousness is apart from law and by faith of Jesus Christ. -/
theorem righteousness_manifested_by_faith :
    manifestRighteousness.righteousnessWithoutLawManifested = true
    ∧ manifestRighteousness.witnessedByLawAndProphets = true
    ∧ manifestRighteousness.byFaithOfJesusChrist = true
    ∧ manifestRighteousness.untoAllAndUponBelievers = true
    ∧ manifestRighteousness.noDifference = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 2: Sin, grace, redemption -/

/-- The universal sin and free justification pattern in Romans 3:23-24. -/
structure GraceRedemptionPattern where
  allHaveSinned : Bool
  comeShortOfGloryOfGod : Bool
  justifiedFreelyByGrace : Bool
  redemptionInChristJesus : Bool
deriving DecidableEq, Repr

/-- All have sinned, and justification is freely by grace through redemption. -/
def graceRedemptionPattern : GraceRedemptionPattern where
  allHaveSinned := true
  comeShortOfGloryOfGod := true
  justifiedFreelyByGrace := true
  redemptionInChristJesus := true

/-- Universal sin is paired with free grace and redemption in Christ Jesus. -/
theorem all_sinned_justified_by_grace :
    graceRedemptionPattern.allHaveSinned = true
    ∧ graceRedemptionPattern.comeShortOfGloryOfGod = true
    ∧ graceRedemptionPattern.justifiedFreelyByGrace = true
    ∧ graceRedemptionPattern.redemptionInChristJesus = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Section 3: Propitiation and declaration -/

/-- The propitiation/declaration pattern in Romans 3:25-26. -/
structure PropitiationDeclaration where
  setForthPropitiation : Bool
  throughFaithInHisBlood : Bool
  declaresRighteousnessForRemissionPastSins : Bool
  throughForbearanceOfGod : Bool
  declaresRighteousnessAtThisTime : Bool
  godIsJust : Bool
  godJustifiesBelieverInJesus : Bool
deriving DecidableEq, Repr

/-- Christ is set forth as propitiation, declaring God's righteousness. -/
def propitiationDeclaration : PropitiationDeclaration where
  setForthPropitiation := true
  throughFaithInHisBlood := true
  declaresRighteousnessForRemissionPastSins := true
  throughForbearanceOfGod := true
  declaresRighteousnessAtThisTime := true
  godIsJust := true
  godJustifiesBelieverInJesus := true

/-- Propitiation is through faith in blood and declares righteousness. -/
theorem propitiation_declares_righteousness :
    propitiationDeclaration.setForthPropitiation = true
    ∧ propitiationDeclaration.throughFaithInHisBlood = true
    ∧ propitiationDeclaration.declaresRighteousnessForRemissionPastSins = true
    ∧ propitiationDeclaration.throughForbearanceOfGod = true
    ∧ propitiationDeclaration.declaresRighteousnessAtThisTime = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- God is just and the justifier of the believer in Jesus. -/
theorem just_and_justifier_of_believer :
    propitiationDeclaration.godIsJust = true
    ∧ propitiationDeclaration.godJustifiesBelieverInJesus = true := by
  exact ⟨rfl, rfl⟩

/-! ## Section 4: Master witness -/

/-- The bounded Romans 3:21-26 witness. -/
theorem romans_righteousness_faith_propitiation_witness :
    manifestRighteousness.righteousnessWithoutLawManifested = true
    ∧ manifestRighteousness.witnessedByLawAndProphets = true
    ∧ manifestRighteousness.byFaithOfJesusChrist = true
    ∧ manifestRighteousness.untoAllAndUponBelievers = true
    ∧ manifestRighteousness.noDifference = true
    ∧ graceRedemptionPattern.allHaveSinned = true
    ∧ graceRedemptionPattern.comeShortOfGloryOfGod = true
    ∧ graceRedemptionPattern.justifiedFreelyByGrace = true
    ∧ graceRedemptionPattern.redemptionInChristJesus = true
    ∧ propitiationDeclaration.setForthPropitiation = true
    ∧ propitiationDeclaration.throughFaithInHisBlood = true
    ∧ propitiationDeclaration.declaresRighteousnessForRemissionPastSins = true
    ∧ propitiationDeclaration.throughForbearanceOfGod = true
    ∧ propitiationDeclaration.declaresRighteousnessAtThisTime = true
    ∧ propitiationDeclaration.godIsJust = true
    ∧ propitiationDeclaration.godJustifiesBelieverInJesus = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · rfl
  · rfl
  · rfl

end RomansRighteousnessFaithPropitiationWitness
end Gnosis.Witnesses.Bible.Romans
