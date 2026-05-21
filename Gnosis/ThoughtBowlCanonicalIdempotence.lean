import Gnosis.ThoughtBowlMultisetEquivalence

/-
  ThoughtBowlCanonicalIdempotence.lean
  ====================================

  Burns down the next-exploration target from
  `ThoughtBowlMultisetEquivalence`: canonicalization is idempotent as
  an actual list, not only at the `bowlOfField` quotient.

  Imports `Gnosis.ThoughtBowlMultisetEquivalence`. Zero `sorry`,
  zero new `axiom`.
-/

namespace ThoughtBowlCanonicalIdempotence

open VibesAsWaveInference
open ThoughtBowlMechanics (bowlOfField)
open ThoughtBowlMechanicsRefined (canonicalField)
open ThoughtBowlMultisetEquivalence

theorem canonicalize_idempotent (waves : List VibeWave) :
    canonicalize (canonicalize waves) = canonicalize waves := by
  change canonicalField (bowlOfField (canonicalize waves)) =
    canonicalField (bowlOfField waves)
  rw [bowl_of_canonicalize_eq_bowl_of_field waves]

theorem canonicalize_fixed_iff_canonicalize_stable (waves : List VibeWave) :
    canonicalize (canonicalize waves) = canonicalize waves ∧
    bowlOfField (canonicalize waves) = bowlOfField waves :=
  ⟨canonicalize_idempotent waves,
    bowl_of_canonicalize_eq_bowl_of_field waves⟩

/-! ## Next exploration

Closed by `Gnosis.ThoughtBowlCanonicalEquivalenceClass`: equal
`bowlOfField` values now yield equal canonicalized lists.
-/

end ThoughtBowlCanonicalIdempotence
