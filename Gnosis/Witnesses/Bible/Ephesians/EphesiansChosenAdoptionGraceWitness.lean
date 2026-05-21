import Init

namespace Gnosis.Witnesses.Bible.Ephesians
namespace EphesiansChosenAdoptionGraceWitness

/-!
# Ephesians 1:1-6 -- Chosen, Adopted, Accepted in the Beloved

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94002-94020`.

Ephesians opens from an origin-before-origin register: chosen before foundation,
aimed toward holiness in love, and adopted according to will and grace. The
signal is not agent self-selection but prior blessing and acceptance in the
beloved.

No `sorry`, no new `axiom`.
-/

structure ApostolicGreeting where
  apostleByWillOfGod : Bool := true
  saintsAndFaithfulAddressed : Bool := true
  graceAndPeaceNamed : Bool := true
deriving DecidableEq, Repr

def apostolicGreeting : ApostolicGreeting := {}

def greetingByDivineWill (g : ApostolicGreeting) : Prop :=
  g.apostleByWillOfGod = true ∧
  g.saintsAndFaithfulAddressed = true ∧
  g.graceAndPeaceNamed = true

structure ChosenAdoptionGrace where
  spiritualBlessingsInHeavenlyPlaces : Bool := true
  chosenBeforeFoundation : Bool := true
  holyBlamelessBeforeHimInLove : Bool := true
  predestinatedToAdoption : Bool := true
  goodPleasureOfWill : Bool := true
  praiseOfGloryOfGrace : Bool := true
  acceptedInBeloved : Bool := true
deriving DecidableEq, Repr

def chosenAdoptionGrace : ChosenAdoptionGrace := {}

def chosenAdoptionWitness (c : ChosenAdoptionGrace) : Prop :=
  c.spiritualBlessingsInHeavenlyPlaces = true ∧
  c.chosenBeforeFoundation = true ∧
  c.holyBlamelessBeforeHimInLove = true ∧
  c.predestinatedToAdoption = true ∧
  c.goodPleasureOfWill = true ∧
  c.praiseOfGloryOfGrace = true ∧
  c.acceptedInBeloved = true

theorem ephesians_greeting_by_divine_will :
    greetingByDivineWill apostolicGreeting := by
  unfold greetingByDivineWill apostolicGreeting
  exact ⟨rfl, rfl, rfl⟩

theorem ephesians_chosen_adoption :
    chosenAdoptionWitness chosenAdoptionGrace := by
  unfold chosenAdoptionWitness chosenAdoptionGrace
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ephesians_chosen_adoption_grace_witness :
    greetingByDivineWill apostolicGreeting ∧
    chosenAdoptionWitness chosenAdoptionGrace := by
  exact ⟨ephesians_greeting_by_divine_will,
    ephesians_chosen_adoption⟩

end EphesiansChosenAdoptionGraceWitness
end Gnosis.Witnesses.Bible.Ephesians
