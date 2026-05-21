import Init

namespace Gnosis.Witnesses.Bible.Ephesians
namespace EphesiansHouseholdOrderWitness

/-!
# Ephesians 6:1-9 -- Children, Parents, Servants, and Masters

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94290-94314`.

Ephesians continues household order but inserts accountability constraints:
promise-bearing honor, non-provocation, service from the heart, and no respect
of persons with the heavenly Master.

No `sorry`, no new `axiom`.
-/

structure HouseholdOrder where
  childrenObeyInLord : Bool := true
  honorFatherMotherPromise : Bool := true
  fathersProvokeNot : Bool := true
  nurtureAdmonitionLord : Bool := true
  servantsObeyAsChrist : Bool := true
  notEyeserviceMenpleasers : Bool := true
  serviceFromHeartToLord : Bool := true
  goodReceivedFromLordBondOrFree : Bool := true
  mastersForbearThreatening : Bool := true
  noRespectOfPersonsWithMaster : Bool := true
deriving DecidableEq, Repr

def householdOrder : HouseholdOrder := {}

def householdOrderWitness (h : HouseholdOrder) : Prop :=
  h.childrenObeyInLord = true ∧ h.honorFatherMotherPromise = true ∧
  h.fathersProvokeNot = true ∧ h.nurtureAdmonitionLord = true ∧
  h.servantsObeyAsChrist = true ∧ h.notEyeserviceMenpleasers = true ∧
  h.serviceFromHeartToLord = true ∧ h.goodReceivedFromLordBondOrFree = true ∧
  h.mastersForbearThreatening = true ∧ h.noRespectOfPersonsWithMaster = true

theorem ephesians_household_order :
    householdOrderWitness householdOrder := by
  unfold householdOrderWitness householdOrder
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EphesiansHouseholdOrderWitness
end Gnosis.Witnesses.Bible.Ephesians
