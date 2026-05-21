import Gnosis.ThoughtBowlCanonicalIdempotence

/-
  ThoughtBowlCanonicalEquivalenceClass.lean
  =========================================

  Burns down the next-exploration target from
  `ThoughtBowlCanonicalIdempotence`: `canonicalize` is the normal form
  for each `bowlOfField` equivalence class.

  Imports `Gnosis.ThoughtBowlCanonicalIdempotence`. Zero `sorry`,
  zero new `axiom`.
-/

namespace ThoughtBowlCanonicalEquivalenceClass

open VibesAsWaveInference
open ThoughtBowlMechanics (bowlOfField)
open ThoughtBowlMechanicsRefined (canonicalField)
open ThoughtBowlMultisetEquivalence
open ThoughtBowlCanonicalIdempotence

theorem same_bowl_implies_same_canonicalize
    {left right : List VibeWave}
    (h : bowlOfField left = bowlOfField right) :
    canonicalize left = canonicalize right := by
  unfold canonicalize
  rw [h]

theorem bowl_equivalent_iff_same_canonicalize
    (left right : List VibeWave) :
    BowlEquivalent left right ↔ canonicalize left = canonicalize right := by
  constructor
  · intro h
    exact same_bowl_implies_same_canonicalize h
  · intro h
    unfold BowlEquivalent
    rw [← bowl_of_canonicalize_eq_bowl_of_field left,
      ← bowl_of_canonicalize_eq_bowl_of_field right, h]

theorem canonicalize_is_normal_form (waves : List VibeWave) :
    BowlEquivalent waves (canonicalize waves) ∧
    canonicalize (canonicalize waves) = canonicalize waves := by
  exact ⟨(bowl_of_canonicalize_eq_bowl_of_field waves).symm,
    canonicalize_idempotent waves⟩

/-! ## Next exploration

Closed by `Gnosis.ThoughtBowlQuotientNormalForm`: the normal form is
now packaged as a quotient-style record with representative stability.
-/

end ThoughtBowlCanonicalEquivalenceClass
