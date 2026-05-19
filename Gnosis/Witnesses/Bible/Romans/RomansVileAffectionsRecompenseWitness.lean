import Init

namespace Gnosis.Witnesses.Bible.Romans
namespace RomansVileAffectionsRecompenseWitness

/-!
# Romans 1:26-27 (KJV) -- Vile Affections and Meet Recompense

This unit gives one bounded consequence topology:

  * for this cause, God gives them up unto vile affections;
  * women change the natural use into that which is against nature;
  * likewise men leave the natural use of the woman;
  * men burn in lust one toward another and work that which is unseemly;
  * they receive in themselves the recompense of their error which is meet.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- Romans 1:26-27 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def romans_1_26_27_quote : String :=
  "1:26 For this cause God gave them up unto vile affections: for " ++
  "even their women did change the natural use into that which is " ++
  "against nature: 1:27 And likewise also the men, leaving the " ++
  "natural use of the woman, burned in their lust one toward another; " ++
  "men with men working that which is unseemly, and receiving in " ++
  "themselves that recompence of their error which was meet."

/-! ## Section 1: Given up for this cause -/

/-- The stated causal consequence in Romans 1:26. -/
structure VileAffectionsConsequence where
  forThisCause : Bool
  godGaveThemUp : Bool
  untoVileAffections : Bool
deriving DecidableEq, Repr

/-- God gives them up unto vile affections for this cause. -/
def vileAffectionsConsequence : VileAffectionsConsequence where
  forThisCause := true
  godGaveThemUp := true
  untoVileAffections := true

/-- The consequence is explicitly causal and divine-giving-up. -/
theorem given_up_unto_vile_affections :
    vileAffectionsConsequence.forThisCause = true
    ∧ vileAffectionsConsequence.godGaveThemUp = true
    ∧ vileAffectionsConsequence.untoVileAffections = true := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Section 2: Changed and left natural use -/

/-- The two natural-use changes named in the unit. -/
inductive NaturalUseChange
  | womenChangedNaturalUseAgainstNature
  | menLeftNaturalUseOfWoman
deriving DecidableEq, Repr

/-- The natural-use changes in source order. -/
def naturalUseChanges : List NaturalUseChange :=
  [ NaturalUseChange.womenChangedNaturalUseAgainstNature
  , NaturalUseChange.menLeftNaturalUseOfWoman
  ]

/-- Women are said to change natural use into what is against nature. -/
theorem women_change_natural_use :
    naturalUseChanges.head? =
      some NaturalUseChange.womenChangedNaturalUseAgainstNature := rfl

/-- Men are said likewise to leave the natural use of the woman. -/
theorem men_leave_natural_use :
    naturalUseChanges.getLast? =
      some NaturalUseChange.menLeftNaturalUseOfWoman := rfl

/-! ## Section 3: Lust, unseemliness, and recompense -/

/-- The conduct and recompense named in Romans 1:27. -/
structure RecompensePattern where
  burnedInLustOneTowardAnother : Bool
  workedUnseemly : Bool
  receivedRecompenseInThemselves : Bool
  errorRecompenseWasMeet : Bool
deriving DecidableEq, Repr

/-- The unit names lust, unseemly work, and a meet recompense. -/
def recompensePattern : RecompensePattern where
  burnedInLustOneTowardAnother := true
  workedUnseemly := true
  receivedRecompenseInThemselves := true
  errorRecompenseWasMeet := true

/-- Lust and unseemly work are named together. -/
theorem lust_and_unseemly_work :
    recompensePattern.burnedInLustOneTowardAnother = true
    ∧ recompensePattern.workedUnseemly = true := by
  exact ⟨rfl, rfl⟩

/-- The recompense is received in themselves and described as meet. -/
theorem recompense_received_and_meet :
    recompensePattern.receivedRecompenseInThemselves = true
    ∧ recompensePattern.errorRecompenseWasMeet = true := by
  exact ⟨rfl, rfl⟩

/-! ## Section 4: Master witness -/

/-- The bounded Romans 1:26-27 witness. -/
theorem romans_vile_affections_recompense_witness :
    vileAffectionsConsequence.forThisCause = true
    ∧ vileAffectionsConsequence.godGaveThemUp = true
    ∧ vileAffectionsConsequence.untoVileAffections = true
    ∧ naturalUseChanges.length = 2
    ∧ naturalUseChanges.head? =
      some NaturalUseChange.womenChangedNaturalUseAgainstNature
    ∧ naturalUseChanges.getLast? =
      some NaturalUseChange.menLeftNaturalUseOfWoman
    ∧ recompensePattern.burnedInLustOneTowardAnother = true
    ∧ recompensePattern.workedUnseemly = true
    ∧ recompensePattern.receivedRecompenseInThemselves = true
    ∧ recompensePattern.errorRecompenseWasMeet = true := by
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

end RomansVileAffectionsRecompenseWitness
end Gnosis.Witnesses.Bible.Romans
