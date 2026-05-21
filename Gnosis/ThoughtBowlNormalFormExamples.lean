import Gnosis.ThoughtBowlQuotientCompleteness

/-
  ThoughtBowlNormalFormExamples.lean
  ==================================

  Burns down the next-exploration target from
  `ThoughtBowlQuotientCompleteness`: concrete examples for reordered
  mixed fields and distinct bowl signatures.

  Imports `Gnosis.ThoughtBowlQuotientCompleteness`. Zero `sorry`,
  zero new `axiom`.
-/

namespace ThoughtBowlNormalFormExamples

open VibesAsWaveInference
open ThoughtBowlMechanics (bowlOfField)
open ThoughtBowlMultisetEquivalence
open ThoughtBowlQuotientNormalForm
open ThoughtBowlQuotientCompleteness

def mixedLeft : List VibeWave :=
  [happyWave, unhappyWave]

def mixedRight : List VibeWave :=
  [unhappyWave, happyWave]

def singletonHappy : List VibeWave :=
  [happyWave]

theorem reordered_mixed_fields_share_normal_form :
    (normalFormOf mixedLeft).normal = (normalFormOf mixedRight).normal := by
  rw [normal_forms_equal_iff_bowl_equivalent]
  unfold BowlEquivalent mixedLeft mixedRight bowlOfField
    ThoughtBowlMechanics.dissentingCount
    ThoughtBowlMechanics.dominantCount
    ThoughtBowlMechanics.minorityCount
    happyCount unhappyCount happyWave unhappyWave
  decide

theorem singleton_and_mixed_have_distinct_bowl_signatures :
    ¬ BowlEquivalent singletonHappy mixedLeft := by
  unfold BowlEquivalent singletonHappy mixedLeft bowlOfField
    ThoughtBowlMechanics.dissentingCount
    ThoughtBowlMechanics.dominantCount
    ThoughtBowlMechanics.minorityCount
    happyCount unhappyCount happyWave unhappyWave
  decide

theorem singleton_and_mixed_have_distinct_normal_forms :
    (normalFormOf singletonHappy).normal ≠ (normalFormOf mixedLeft).normal := by
  intro h
  exact singleton_and_mixed_have_distinct_bowl_signatures
    ((normal_forms_equal_iff_bowl_equivalent singletonHappy mixedLeft).mp h)

theorem normal_form_examples_witness :
    (normalFormOf mixedLeft).normal = (normalFormOf mixedRight).normal ∧
    (normalFormOf singletonHappy).normal ≠ (normalFormOf mixedLeft).normal :=
  ⟨reordered_mixed_fields_share_normal_form,
    singleton_and_mixed_have_distinct_normal_forms⟩

/-! ## Next exploration

The thought-bowl canonicalization chain is closed at the finite
normal-form level. The next honest extension is no longer a local
normal-form theorem; an actual quotient type is outside this Rustic
module.
-/

end ThoughtBowlNormalFormExamples
