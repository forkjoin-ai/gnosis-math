import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansElementsRelapseWitness

/-!
# Galatians 4:8-11 -- Known by God and Relapse into Elements

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93806-93819`.

The relapse is framed as an antitheorem of recognition: once known by God, the
return to weak and beggarly elements is not progress but re-bondage. Calendar
observance becomes evidence of capture when it replaces sonship with element
accounting.

No `sorry`, no new `axiom`.
-/

structure FormerElementService where
  knewNotGod : Bool := true
  servedNoGodsByNature : Bool := true
deriving DecidableEq, Repr

def formerElementService : FormerElementService := {}

def formerServiceWitness (f : FormerElementService) : Prop :=
  f.knewNotGod = true ∧
  f.servedNoGodsByNature = true

structure RelapseToElements where
  knownGodOrRatherKnownByGod : Bool := true
  turnAgainToWeakElements : Bool := true
  beggarlyElementsNamed : Bool := true
  desireBondageAgain : Bool := true
  daysMonthsTimesYearsObserved : Bool := true
  apostolicLaborAtRiskOfVain : Bool := true
deriving DecidableEq, Repr

def relapseToElements : RelapseToElements := {}

def elementRelapseGap (r : RelapseToElements) : Prop :=
  r.knownGodOrRatherKnownByGod = true ∧
  r.turnAgainToWeakElements = true ∧
  r.beggarlyElementsNamed = true ∧
  r.desireBondageAgain = true ∧
  r.daysMonthsTimesYearsObserved = true ∧
  r.apostolicLaborAtRiskOfVain = true

theorem galatians_former_service :
    formerServiceWitness formerElementService := by
  unfold formerServiceWitness formerElementService
  exact ⟨rfl, rfl⟩

theorem galatians_element_relapse_gap :
    elementRelapseGap relapseToElements := by
  unfold elementRelapseGap relapseToElements
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_elements_relapse_witness :
    formerServiceWitness formerElementService ∧
    elementRelapseGap relapseToElements := by
  exact ⟨galatians_former_service,
    galatians_element_relapse_gap⟩

end GalatiansElementsRelapseWitness
end Gnosis.Witnesses.Bible.Galatians
