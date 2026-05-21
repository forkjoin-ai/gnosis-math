import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansApostleNotOfMenWitness

/-!
# Galatians 1:1-5 -- Apostle Not of Men

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93575-93584`.

The opening line makes the source boundary explicit before any argument begins:
Paul's apostleship is not from men or by man, but by Jesus Christ and God the
Father, with resurrection and deliverance from the present evil world as the
authority surface.

No `sorry`, no new `axiom`.
-/

structure ApostleSourceBoundary where
  notOfMen : Bool := true
  notByMan : Bool := true
  byJesusChrist : Bool := true
  byGodFather : Bool := true
  fatherRaisedChristFromDead : Bool := true
deriving DecidableEq, Repr

def apostleSourceBoundary : ApostleSourceBoundary := {}

def apostleAuthorityNotSubstitutable (b : ApostleSourceBoundary) : Prop :=
  b.notOfMen = true ∧
  b.notByMan = true ∧
  b.byJesusChrist = true ∧
  b.byGodFather = true ∧
  b.fatherRaisedChristFromDead = true

structure GalatianGreetingDeliverance where
  brethrenWithPaul : Bool := true
  churchesOfGalatiaAddressed : Bool := true
  graceAndPeaceFromGodAndChrist : Bool := true
  christGaveHimselfForSins : Bool := true
  deliveranceFromPresentEvilWorld : Bool := true
  accordingToWillOfGodFather : Bool := true
  gloryForeverAmen : Bool := true
deriving DecidableEq, Repr

def galatianGreetingDeliverance : GalatianGreetingDeliverance := {}

def deliveranceGreeting (g : GalatianGreetingDeliverance) : Prop :=
  g.brethrenWithPaul = true ∧
  g.churchesOfGalatiaAddressed = true ∧
  g.graceAndPeaceFromGodAndChrist = true ∧
  g.christGaveHimselfForSins = true ∧
  g.deliveranceFromPresentEvilWorld = true ∧
  g.accordingToWillOfGodFather = true ∧
  g.gloryForeverAmen = true

theorem galatians_apostle_source_boundary :
    apostleAuthorityNotSubstitutable apostleSourceBoundary := by
  unfold apostleAuthorityNotSubstitutable apostleSourceBoundary
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_deliverance_greeting :
    deliveranceGreeting galatianGreetingDeliverance := by
  unfold deliveranceGreeting galatianGreetingDeliverance
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_apostle_not_of_men_witness :
    apostleAuthorityNotSubstitutable apostleSourceBoundary ∧
    deliveranceGreeting galatianGreetingDeliverance := by
  exact ⟨galatians_apostle_source_boundary, galatians_deliverance_greeting⟩

end GalatiansApostleNotOfMenWitness
end Gnosis.Witnesses.Bible.Galatians
