import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansCrossNewCreationWitness

/-!
# Galatians 6:11-18 -- Flesh Boast, Cross Glory, and New Creation

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93977-94001`.

The closing signature exposes circumcision pressure as persecution-avoidance and
flesh-boasting. The positive rule is not circumcision or uncircumcision but new
creation, with the cross as the only allowed boast.

No `sorry`, no new `axiom`.
-/

structure FleshBoastPressure where
  largeOwnHandLetter : Bool := true
  fairShowInFleshDesired : Bool := true
  circumcisionConstrained : Bool := true
  crossPersecutionAvoided : Bool := true
  circumcisedDoNotKeepLaw : Bool := true
  gloryInYourFleshDesired : Bool := true
deriving DecidableEq, Repr

def fleshBoastPressure : FleshBoastPressure := {}

def fleshBoastCapture (f : FleshBoastPressure) : Prop :=
  f.largeOwnHandLetter = true ∧
  f.fairShowInFleshDesired = true ∧
  f.circumcisionConstrained = true ∧
  f.crossPersecutionAvoided = true ∧
  f.circumcisedDoNotKeepLaw = true ∧
  f.gloryInYourFleshDesired = true

structure CrossNewCreation where
  gloryOnlyInCross : Bool := true
  worldCrucifiedToPaul : Bool := true
  paulCrucifiedToWorld : Bool := true
  circumcisionAvailsNothing : Bool := true
  uncircumcisionAvailsNothing : Bool := true
  newCreatureAvails : Bool := true
  peaceMercyOnRuleWalkers : Bool := true
  marksOfLordJesusBorne : Bool := true
  graceWithSpiritClosing : Bool := true
deriving DecidableEq, Repr

def crossNewCreation : CrossNewCreation := {}

def newCreationRule (c : CrossNewCreation) : Prop :=
  c.gloryOnlyInCross = true ∧
  c.worldCrucifiedToPaul = true ∧
  c.paulCrucifiedToWorld = true ∧
  c.circumcisionAvailsNothing = true ∧
  c.uncircumcisionAvailsNothing = true ∧
  c.newCreatureAvails = true ∧
  c.peaceMercyOnRuleWalkers = true ∧
  c.marksOfLordJesusBorne = true ∧
  c.graceWithSpiritClosing = true

theorem galatians_flesh_boast_capture :
    fleshBoastCapture fleshBoastPressure := by
  unfold fleshBoastCapture fleshBoastPressure
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_new_creation_rule :
    newCreationRule crossNewCreation := by
  unfold newCreationRule crossNewCreation
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_cross_new_creation_witness :
    fleshBoastCapture fleshBoastPressure ∧
    newCreationRule crossNewCreation := by
  exact ⟨galatians_flesh_boast_capture,
    galatians_new_creation_rule⟩

end GalatiansCrossNewCreationWitness
end Gnosis.Witnesses.Bible.Galatians
