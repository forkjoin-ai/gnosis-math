import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansAnotherGospelBoundaryWitness

/-!
# Galatians 1:6-12 -- Another Gospel Boundary

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93586-93605`.

This is a direct anti-substitution witness. "Another gospel" is immediately
denied as a true alternate; it is trouble and perversion. Even an angelic
messenger cannot override the received gospel boundary.

No `sorry`, no new `axiom`.
-/

structure GospelBoundary where
  removedFromGraceIsMarvelledAt : Bool := true
  anotherGospelIsNotAnother : Bool := true
  troublersPervertGospel : Bool := true
  angelicOverrideRejected : Bool := true
  repeatedAnathemaBoundary : Bool := true
deriving DecidableEq, Repr

def gospelBoundary : GospelBoundary := {}

def anotherGospelIsCounterfeit (b : GospelBoundary) : Prop :=
  b.removedFromGraceIsMarvelledAt = true ∧
  b.anotherGospelIsNotAnother = true ∧
  b.troublersPervertGospel = true ∧
  b.angelicOverrideRejected = true ∧
  b.repeatedAnathemaBoundary = true

structure HumanPleasingGap where
  persuasionOfMenOpposedToGod : Bool := true
  pleasingMenContradictsServantOfChrist : Bool := true
  gospelNotAfterMan : Bool := true
  gospelNotReceivedOfMan : Bool := true
  gospelNotTaughtByMan : Bool := true
  revelationOfJesusChristNamed : Bool := true
deriving DecidableEq, Repr

def humanPleasingGap : HumanPleasingGap := {}

def humanSourceGapExposed (g : HumanPleasingGap) : Prop :=
  g.persuasionOfMenOpposedToGod = true ∧
  g.pleasingMenContradictsServantOfChrist = true ∧
  g.gospelNotAfterMan = true ∧
  g.gospelNotReceivedOfMan = true ∧
  g.gospelNotTaughtByMan = true ∧
  g.revelationOfJesusChristNamed = true

theorem galatians_another_gospel_counterfeit :
    anotherGospelIsCounterfeit gospelBoundary := by
  unfold anotherGospelIsCounterfeit gospelBoundary
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_human_source_gap :
    humanSourceGapExposed humanPleasingGap := by
  unfold humanSourceGapExposed humanPleasingGap
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_another_gospel_boundary_witness :
    anotherGospelIsCounterfeit gospelBoundary ∧
    humanSourceGapExposed humanPleasingGap := by
  exact ⟨galatians_another_gospel_counterfeit, galatians_human_source_gap⟩

end GalatiansAnotherGospelBoundaryWitness
end Gnosis.Witnesses.Bible.Galatians
