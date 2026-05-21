import Gnosis.ThoughtBowlCanonicalEquivalenceClass

/-
  ThoughtBowlQuotientNormalForm.lean
  ==================================

  Burns down the next-exploration target from
  `ThoughtBowlCanonicalEquivalenceClass`: package a representative,
  its canonical field, and the proof that every equivalent
  representative canonicalizes to the same list.

  Imports `Gnosis.ThoughtBowlCanonicalEquivalenceClass`. Zero `sorry`,
  zero new `axiom`.
-/

namespace ThoughtBowlQuotientNormalForm

open VibesAsWaveInference
open ThoughtBowlMechanics (bowlOfField)
open ThoughtBowlMultisetEquivalence
open ThoughtBowlCanonicalEquivalenceClass

/-- A quotient-style normal-form package for the bowl equivalence class
    of a concrete field. -/
structure BowlNormalForm where
  representative : List VibeWave
  normal         : List VibeWave
  normalized     : canonicalize representative = normal
  stable         : canonicalize normal = normal
  classInvariant :
    ∀ candidate : List VibeWave,
      BowlEquivalent candidate representative → canonicalize candidate = normal

def normalFormOf (waves : List VibeWave) : BowlNormalForm :=
  { representative := waves
    normal := canonicalize waves
    normalized := rfl
    stable := ThoughtBowlCanonicalIdempotence.canonicalize_idempotent waves
    classInvariant := by
      intro candidate h
      exact same_bowl_implies_same_canonicalize h }

theorem normal_form_class_invariant
    (waves candidate : List VibeWave)
    (h : BowlEquivalent candidate waves) :
    canonicalize candidate = (normalFormOf waves).normal :=
  (normalFormOf waves).classInvariant candidate h

theorem normal_form_stable (waves : List VibeWave) :
    canonicalize (normalFormOf waves).normal = (normalFormOf waves).normal :=
  (normalFormOf waves).stable

/-! ## Next exploration

Closed by `Gnosis.ThoughtBowlQuotientSoundness`: equal normal fields
now imply the same `BowlEquivalent` class.
-/

end ThoughtBowlQuotientNormalForm
