import Gnosis.ThoughtBowlQuotientSoundness

/-
  ThoughtBowlQuotientCompleteness.lean
  ====================================

  Burns down the next-exploration target from
  `ThoughtBowlQuotientSoundness`: equality of normal forms is exactly
  `BowlEquivalent`.

  Imports `Gnosis.ThoughtBowlQuotientSoundness`. Zero `sorry`, zero
  new `axiom`.
-/

namespace ThoughtBowlQuotientCompleteness

open VibesAsWaveInference
open ThoughtBowlMultisetEquivalence
open ThoughtBowlQuotientNormalForm
open ThoughtBowlQuotientSoundness

/-- The quotient-normal-form theorem: two fields are in the same
    bowl-equivalence class exactly when their normal forms are equal. -/
theorem normal_forms_equal_iff_bowl_equivalent
    (left right : List VibeWave) :
    (normalFormOf left).normal = (normalFormOf right).normal ↔
      BowlEquivalent left right :=
  same_normal_iff_bowl_equivalent left right

theorem quotient_normal_form_witness (waves : List VibeWave) :
    BowlEquivalent waves (normalFormOf waves).normal ∧
    (normalFormOf (normalFormOf waves).normal).normal =
      (normalFormOf waves).normal := by
  refine ⟨?_, ?_⟩
  · exact (ThoughtBowlMultisetEquivalence.canonicalize_is_bowl_equivalent waves).symm
  · exact ThoughtBowlCanonicalIdempotence.canonicalize_idempotent waves

/-! ## Next exploration

Closed by `Gnosis.ThoughtBowlNormalFormExamples`: reordered fields now
share a concrete normal-form example, while different signatures do not.
-/

end ThoughtBowlQuotientCompleteness
