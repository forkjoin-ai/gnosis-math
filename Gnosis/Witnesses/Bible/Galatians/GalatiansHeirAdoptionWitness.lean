import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansHeirAdoptionWitness

/-!
# Galatians 4:1-7 -- Heir, Tutor, Adoption, and Spirit Cry

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93786-93805`.

The child-heir image continues the schoolmaster boundary: an heir can be lord of
all and still functionally indistinguishable from a servant until the appointed
time. Adoption is the runtime transition from custody to sonship.

No `sorry`, no new `axiom`.
-/

structure ChildHeirCustody where
  heirAsChildDiffersNothingFromServant : Bool := true
  lordOfAllYetUnderTutors : Bool := true
  appointedTimeOfFather : Bool := true
  bondageUnderWorldElements : Bool := true
deriving DecidableEq, Repr

def childHeirCustody : ChildHeirCustody := {}

def custodyBeforeAppointment (c : ChildHeirCustody) : Prop :=
  c.heirAsChildDiffersNothingFromServant = true ∧
  c.lordOfAllYetUnderTutors = true ∧
  c.appointedTimeOfFather = true ∧
  c.bondageUnderWorldElements = true

structure AdoptionTransition where
  fullnessOfTimeCame : Bool := true
  sonSentMadeOfWoman : Bool := true
  sonMadeUnderLaw : Bool := true
  underLawRedeemed : Bool := true
  adoptionOfSonsReceived : Bool := true
  spiritSentIntoHearts : Bool := true
  abbaFatherCry : Bool := true
  noMoreServantButSonHeir : Bool := true
deriving DecidableEq, Repr

def adoptionTransition : AdoptionTransition := {}

def adoptionHeirshipWitness (a : AdoptionTransition) : Prop :=
  a.fullnessOfTimeCame = true ∧
  a.sonSentMadeOfWoman = true ∧
  a.sonMadeUnderLaw = true ∧
  a.underLawRedeemed = true ∧
  a.adoptionOfSonsReceived = true ∧
  a.spiritSentIntoHearts = true ∧
  a.abbaFatherCry = true ∧
  a.noMoreServantButSonHeir = true

theorem galatians_custody_before_appointment :
    custodyBeforeAppointment childHeirCustody := by
  unfold custodyBeforeAppointment childHeirCustody
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem galatians_adoption_heirship :
    adoptionHeirshipWitness adoptionTransition := by
  unfold adoptionHeirshipWitness adoptionTransition
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_heir_adoption_witness :
    custodyBeforeAppointment childHeirCustody ∧
    adoptionHeirshipWitness adoptionTransition := by
  exact ⟨galatians_custody_before_appointment,
    galatians_adoption_heirship⟩

end GalatiansHeirAdoptionWitness
end Gnosis.Witnesses.Bible.Galatians
