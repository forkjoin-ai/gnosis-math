import Init

namespace Gnosis.Witnesses.Bible.FirstTimothy
namespace FirstTimothyWidowsEldersPurityWitness

/-!
# 1 Timothy 5 -- Widows, Elders, Partiality, and Manifest Works

Source text: `docs/ebooks/source-texts/bible-kjv.txt:95465-95545`.

The household of truth must distinguish real need from disorderly burden-shift.
Care, honour, accusation, rebuke, ordination, partiality, visible sin, and visible
good works all become discernment tests.

No `sorry`, no new `axiom`.
-/

structure HouseholdCare where
  eldersTreatedAsFamily : Bool := true
  widowsIndeedHonored : Bool := true
  familyFirstRequitesParents : Bool := true
  desolateWidowTrustsGod : Bool := true
  pleasureLivingDeadNamed : Bool := true
  ownHouseProvisionRequired : Bool := true
  goodWorksQualifyWidowLedger : Bool := true
  idlenessBusybodyRiskNamed : Bool := true
  churchRelievesWidowsIndeed : Bool := true
deriving DecidableEq, Repr

def householdCare : HouseholdCare := {}

def householdCareWitness (h : HouseholdCare) : Prop :=
  h.eldersTreatedAsFamily = true ∧ h.widowsIndeedHonored = true ∧
  h.familyFirstRequitesParents = true ∧ h.desolateWidowTrustsGod = true ∧
  h.pleasureLivingDeadNamed = true ∧ h.ownHouseProvisionRequired = true ∧
  h.goodWorksQualifyWidowLedger = true ∧ h.idlenessBusybodyRiskNamed = true ∧
  h.churchRelievesWidowsIndeed = true

structure ElderPurityDiscernment where
  rulingEldersDoubleHonour : Bool := true
  laborerRewardScripture : Bool := true
  accusationByWitnesses : Bool := true
  publicRebukeForFear : Bool := true
  nothingByPartiality : Bool := true
  handsNotSudden : Bool := true
  purityKept : Bool := true
  sinsAndGoodWorksManifest : Bool := true
deriving DecidableEq, Repr

def elderPurityDiscernment : ElderPurityDiscernment := {}

def elderPurityWitness (e : ElderPurityDiscernment) : Prop :=
  e.rulingEldersDoubleHonour = true ∧ e.laborerRewardScripture = true ∧
  e.accusationByWitnesses = true ∧ e.publicRebukeForFear = true ∧
  e.nothingByPartiality = true ∧ e.handsNotSudden = true ∧
  e.purityKept = true ∧ e.sinsAndGoodWorksManifest = true

theorem first_timothy_household_care :
    householdCareWitness householdCare := by
  unfold householdCareWitness householdCare
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_timothy_elder_purity :
    elderPurityWitness elderPurityDiscernment := by
  unfold elderPurityWitness elderPurityDiscernment
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_timothy_widows_elders_purity_witness :
    householdCareWitness householdCare ∧ elderPurityWitness elderPurityDiscernment := by
  exact ⟨first_timothy_household_care, first_timothy_elder_purity⟩

end FirstTimothyWidowsEldersPurityWitness
end Gnosis.Witnesses.Bible.FirstTimothy
