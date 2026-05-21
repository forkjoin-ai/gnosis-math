import Gnosis.ThoughtBowlQuotientNormalForm

/-
  ThoughtBowlQuotientSoundness.lean
  =================================

  Burns down the next-exploration target from
  `ThoughtBowlQuotientNormalForm`: equal normal forms imply equal
  `BowlEquivalent` classes.

  Imports `Gnosis.ThoughtBowlQuotientNormalForm`. Zero `sorry`,
  zero new `axiom`.
-/

namespace ThoughtBowlQuotientSoundness

open VibesAsWaveInference
open ThoughtBowlMultisetEquivalence
open ThoughtBowlCanonicalEquivalenceClass
open ThoughtBowlQuotientNormalForm

theorem equal_normal_forms_sound
    (left right : BowlNormalForm)
    (h : left.normal = right.normal) :
    BowlEquivalent left.representative right.representative := by
  rw [bowl_equivalent_iff_same_canonicalize]
  rw [left.normalized, right.normalized, h]

theorem normal_form_of_equal_normal_sound
    (left right : List VibeWave)
    (h : (normalFormOf left).normal = (normalFormOf right).normal) :
    BowlEquivalent left right :=
  equal_normal_forms_sound (normalFormOf left) (normalFormOf right) h

theorem same_normal_iff_bowl_equivalent
    (left right : List VibeWave) :
    (normalFormOf left).normal = (normalFormOf right).normal ↔
      BowlEquivalent left right := by
  constructor
  · intro h
    exact normal_form_of_equal_normal_sound left right h
  · intro h
    exact same_bowl_implies_same_canonicalize h

/-! ## Next exploration

Closed by `Gnosis.ThoughtBowlQuotientCompleteness`: equality of normal
forms is now equivalent to `BowlEquivalent`.
-/

end ThoughtBowlQuotientSoundness
