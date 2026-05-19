import Init

namespace Gnosis.Witnesses.Bible.Romans
namespace RomansReprobateMindJudgmentWitness

/-!
# Romans 1:28-32 (KJV) -- Reprobate Mind and Judgment

This unit gives one bounded catalogue topology:

  * they do not like to retain God in their knowledge;
  * God gives them over to a reprobate mind;
  * the passage enumerates the deeds done under that mind;
  * the closing clause names knowledge of judgment, worthiness of death,
    doing the same, and taking pleasure in those who do them.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- Romans 1:28-32 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def romans_1_28_32_quote : String :=
  "1:28 And even as they did not like to retain God in their knowledge, " ++
  "God gave them over to a reprobate mind, to do those things which are " ++
  "not convenient; 1:29 Being filled with all unrighteousness, " ++
  "fornication, wickedness, covetousness, maliciousness; full of envy, " ++
  "murder, debate, deceit, malignity; whisperers, 1:30 Backbiters, haters " ++
  "of God, despiteful, proud, boasters, inventors of evil things, " ++
  "disobedient to parents, 1:31 Without understanding, covenantbreakers, " ++
  "without natural affection, implacable, unmerciful: 1:32 Who knowing " ++
  "the judgment of God, that they which commit such things are worthy of " ++
  "death, not only do the same, but have pleasure in them that do them."

/-! ## Section 1: Given over to reprobate mind -/

/-- The antecedent and consequence named in Romans 1:28. -/
structure ReprobateMindConsequence where
  didNotRetainGodInKnowledge : Bool
  godGaveThemOver : Bool
  toReprobateMind : Bool
  toDoThingsNotConvenient : Bool
deriving DecidableEq, Repr

/-- Romans 1:28 binds not-retaining knowledge to being given over. -/
def reprobateMindConsequence : ReprobateMindConsequence where
  didNotRetainGodInKnowledge := true
  godGaveThemOver := true
  toReprobateMind := true
  toDoThingsNotConvenient := true

/-- The consequence is knowledge-refusal followed by being given over. -/
theorem reprobate_mind_given_over :
    reprobateMindConsequence.didNotRetainGodInKnowledge = true
    ∧ reprobateMindConsequence.godGaveThemOver = true
    ∧ reprobateMindConsequence.toReprobateMind = true
    ∧ reprobateMindConsequence.toDoThingsNotConvenient = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Section 2: The unrighteousness catalogue -/

/-- The named items in the Romans 1:29-31 catalogue, in source order. -/
inductive ReprobateCatalogueItem
  | unrighteousness
  | fornication
  | wickedness
  | covetousness
  | maliciousness
  | envy
  | murder
  | debate
  | deceit
  | malignity
  | whisperers
  | backbiters
  | hatersOfGod
  | despiteful
  | proud
  | boasters
  | inventorsOfEvilThings
  | disobedientToParents
  | withoutUnderstanding
  | covenantbreakers
  | withoutNaturalAffection
  | implacable
  | unmerciful
deriving DecidableEq, Repr

/-- The Romans 1:29-31 catalogue in source order. -/
def reprobateCatalogue : List ReprobateCatalogueItem :=
  [ ReprobateCatalogueItem.unrighteousness
  , ReprobateCatalogueItem.fornication
  , ReprobateCatalogueItem.wickedness
  , ReprobateCatalogueItem.covetousness
  , ReprobateCatalogueItem.maliciousness
  , ReprobateCatalogueItem.envy
  , ReprobateCatalogueItem.murder
  , ReprobateCatalogueItem.debate
  , ReprobateCatalogueItem.deceit
  , ReprobateCatalogueItem.malignity
  , ReprobateCatalogueItem.whisperers
  , ReprobateCatalogueItem.backbiters
  , ReprobateCatalogueItem.hatersOfGod
  , ReprobateCatalogueItem.despiteful
  , ReprobateCatalogueItem.proud
  , ReprobateCatalogueItem.boasters
  , ReprobateCatalogueItem.inventorsOfEvilThings
  , ReprobateCatalogueItem.disobedientToParents
  , ReprobateCatalogueItem.withoutUnderstanding
  , ReprobateCatalogueItem.covenantbreakers
  , ReprobateCatalogueItem.withoutNaturalAffection
  , ReprobateCatalogueItem.implacable
  , ReprobateCatalogueItem.unmerciful
  ]

/-- The catalogue begins with unrighteousness. -/
theorem catalogue_begins_with_unrighteousness :
    reprobateCatalogue.head? = some ReprobateCatalogueItem.unrighteousness := rfl

/-- The catalogue closes with unmerciful. -/
theorem catalogue_closes_with_unmerciful :
    reprobateCatalogue.getLast? = some ReprobateCatalogueItem.unmerciful := rfl

/-- The witness keeps all twenty-three named catalogue items. -/
theorem catalogue_item_count :
    reprobateCatalogue.length = 23 := rfl

/-! ## Section 3: Judgment and approval of doing -/

/-- Romans 1:32 closes with judgment, doing, and pleasure in doers. -/
structure JudgmentApprovalPattern where
  knowingJudgmentOfGod : Bool
  worthyOfDeath : Bool
  doTheSame : Bool
  havePleasureInDoers : Bool
deriving DecidableEq, Repr

/-- The final judgment pattern named in Romans 1:32. -/
def judgmentApprovalPattern : JudgmentApprovalPattern where
  knowingJudgmentOfGod := true
  worthyOfDeath := true
  doTheSame := true
  havePleasureInDoers := true

/-- The passage states knowing judgment and worthiness of death. -/
theorem knowing_judgment_and_worthy_of_death :
    judgmentApprovalPattern.knowingJudgmentOfGod = true
    ∧ judgmentApprovalPattern.worthyOfDeath = true := by
  exact ⟨rfl, rfl⟩

/-- The passage adds both doing the same and pleasure in those who do. -/
theorem doing_and_approval_pattern :
    judgmentApprovalPattern.doTheSame = true
    ∧ judgmentApprovalPattern.havePleasureInDoers = true := by
  exact ⟨rfl, rfl⟩

/-! ## Section 4: Master witness -/

/-- The bounded Romans 1:28-32 witness. -/
theorem romans_reprobate_mind_judgment_witness :
    reprobateMindConsequence.didNotRetainGodInKnowledge = true
    ∧ reprobateMindConsequence.godGaveThemOver = true
    ∧ reprobateMindConsequence.toReprobateMind = true
    ∧ reprobateMindConsequence.toDoThingsNotConvenient = true
    ∧ reprobateCatalogue.length = 23
    ∧ reprobateCatalogue.head? = some ReprobateCatalogueItem.unrighteousness
    ∧ reprobateCatalogue.getLast? = some ReprobateCatalogueItem.unmerciful
    ∧ judgmentApprovalPattern.knowingJudgmentOfGod = true
    ∧ judgmentApprovalPattern.worthyOfDeath = true
    ∧ judgmentApprovalPattern.doTheSame = true
    ∧ judgmentApprovalPattern.havePleasureInDoers = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

end RomansReprobateMindJudgmentWitness
end Gnosis.Witnesses.Bible.Romans
