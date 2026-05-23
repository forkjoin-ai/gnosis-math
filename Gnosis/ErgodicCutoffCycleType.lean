import Init
import Gnosis.AeonNoise
import Gnosis.ErgodicCutoffDuality

/-!
# Ergodic Cutoff — the antitheorem: same period, provably different action

This is the negative half of [`ErgodicCutoffDuality`](Gnosis/ErgodicCutoffDuality.lean).
The pitch says the Arnold cat map on `(Z/5)²` and the perfect out-shuffle on 12 cards
are "the same finite torus automorphism quotient" because both have period 10. The
period really does match — `cat_returns_all_10`, `shuffle_returns_all_10`. So this is
exactly the dangerous kind of near-miss: a coincidence of magnitude that *looks* like
an identity.

The job of this module is the **antitheorem** — to certify, against the apparent match,
that there is no match underneath:

* **Positive (the genuine shared structure).** Both maps realize a cyclic group of order
  *exactly* 10: their set of periods is precisely the multiples of 10
  (`cat_period_iff`, `shuffle_period_iff`). This is the most that is actually shared.
* **Antitheorem (the refuted identity).** Two permutations with the same order are
  conjugate only if their cycle types agree. They do not:
  the cat map has cycle type `1 + 2 + 2 + 10 + 10` and the out-shuffle `1 + 1 + 10`.
  We certify this through the conjugacy invariant "number of points fixed by `f^d`":
  the profiles `(f¹,f²,f⁵,f¹⁰) = (1,5,1,25)` versus `(2,2,2,12)` disagree in every slot
  (`cat_fix_profile`, `shuffle_fix_profile`, `actions_are_not_conjugate`).

So "same period" is a theorem and "same quotient" is an antitheorem. The seeming match is
refuted at the granularity where `lake build` still bears weight.

Zero `sorry`. Zero `omega`. Zero Mathlib.
-/

namespace Gnosis
namespace ErgodicCutoffCycleType

open Gnosis.AeonNoise
open Gnosis.ErgodicCutoffDuality
open Gnosis.FiniteDynamicsCore

/-! The period machinery (`ReturnsAll`, `period_dvd`, `returnsAll_of_dvd`, `countFixedBy`)
and the antitheorem schema (`separates`) live in `Gnosis/FiniteDynamicsCore.lean`; this
module supplies the cat-map and out-shuffle *instances* and the conjugacy refutation. -/

-- ═══════════════════════════════════════════════════════════════════════
-- §2  The cat map — order exactly 10, cycle type 1+2+2+10+10
-- ═══════════════════════════════════════════════════════════════════════

theorem cat_carrier_closed : ∀ p ∈ catCarrier, aeonCatMap p ∈ catCarrier := by decide

theorem cat_returns_all_10 : ReturnsAll aeonCatMap catCarrier 10 := by
  unfold ReturnsAll; decide

theorem cat_no_small_period :
    ∀ d, d < 10 → 0 < d → ¬ ReturnsAll aeonCatMap catCarrier d := by
  unfold ReturnsAll; decide

/-- The periods of the cat map are exactly the multiples of 10 — order exactly 10. -/
theorem cat_period_iff (T : Nat) :
    ReturnsAll aeonCatMap catCarrier T ↔ 10 ∣ T := by
  constructor
  · exact period_dvd aeonCatMap catCarrier 10 (by decide) cat_carrier_closed
      cat_returns_all_10 cat_no_small_period T
  · intro h
    exact returnsAll_of_dvd aeonCatMap catCarrier 10 T h cat_returns_all_10

/-- Cat-map fixed-point profile: `(f¹,f²,f⁵,f¹⁰) = (1,5,1,25)` — cycle type 1+2+2+10+10. -/
theorem cat_fix_profile :
    countFixedBy aeonCatMap catCarrier 1 = 1 ∧
    countFixedBy aeonCatMap catCarrier 2 = 5 ∧
    countFixedBy aeonCatMap catCarrier 5 = 1 ∧
    countFixedBy aeonCatMap catCarrier 10 = 25 := by decide

-- ═══════════════════════════════════════════════════════════════════════
-- §3  The out-shuffle — order exactly 10, cycle type 1+1+10
-- ═══════════════════════════════════════════════════════════════════════

theorem shuffle_carrier_closed :
    ∀ i ∈ shuffleCarrier, outShuffle12 i ∈ shuffleCarrier := by decide

theorem shuffle_returns_all_10 : ReturnsAll outShuffle12 shuffleCarrier 10 := by
  unfold ReturnsAll; decide

theorem shuffle_no_small_period :
    ∀ d, d < 10 → 0 < d → ¬ ReturnsAll outShuffle12 shuffleCarrier d := by
  unfold ReturnsAll; decide

/-- The periods of the out-shuffle are exactly the multiples of 10 — order exactly 10. -/
theorem shuffle_period_iff (T : Nat) :
    ReturnsAll outShuffle12 shuffleCarrier T ↔ 10 ∣ T := by
  constructor
  · exact period_dvd outShuffle12 shuffleCarrier 10 (by decide) shuffle_carrier_closed
      shuffle_returns_all_10 shuffle_no_small_period T
  · intro h
    exact returnsAll_of_dvd outShuffle12 shuffleCarrier 10 T h shuffle_returns_all_10

/-- Out-shuffle fixed-point profile: `(f¹,f²,f⁵,f¹⁰) = (2,2,2,12)` — cycle type 1+1+10. -/
theorem shuffle_fix_profile :
    countFixedBy outShuffle12 shuffleCarrier 1 = 2 ∧
    countFixedBy outShuffle12 shuffleCarrier 2 = 2 ∧
    countFixedBy outShuffle12 shuffleCarrier 5 = 2 ∧
    countFixedBy outShuffle12 shuffleCarrier 10 = 12 := by decide

-- ═══════════════════════════════════════════════════════════════════════
-- §4  The antitheorem — the seeming match has no match underneath
-- ═══════════════════════════════════════════════════════════════════════

/-- **Antitheorem.** The cat map and the out-shuffle are *not* conjugate permutations:
    a conjugacy invariant (points fixed by `f²`) disagrees, 5 ≠ 2. Despite sharing order
    exactly 10, they realize different actions of `C₁₀`, so they are not "the same
    quotient." The apparent numerical match (period 10) is refuted at the structure level. -/
theorem actions_are_not_conjugate :
    countFixedBy aeonCatMap catCarrier 2 ≠ countFixedBy outShuffle12 shuffleCarrier 2 := by
  decide

/--
Master bundle. The seeming match is true exactly to the depth of "order 10" and no further:

* both realize `C₁₀` (period set = multiples of 10), the genuine shared structure;
* their cycle-type fingerprints differ in every slot, so the identity is an antitheorem.
-/
theorem same_order_different_action :
    (∀ T, ReturnsAll aeonCatMap catCarrier T ↔ 10 ∣ T) ∧
    (∀ T, ReturnsAll outShuffle12 shuffleCarrier T ↔ 10 ∣ T) ∧
    (countFixedBy aeonCatMap catCarrier 1 ≠ countFixedBy outShuffle12 shuffleCarrier 1) ∧
    (countFixedBy aeonCatMap catCarrier 2 ≠ countFixedBy outShuffle12 shuffleCarrier 2) ∧
    (countFixedBy aeonCatMap catCarrier 5 ≠ countFixedBy outShuffle12 shuffleCarrier 5) ∧
    (countFixedBy aeonCatMap catCarrier 10 ≠ countFixedBy outShuffle12 shuffleCarrier 10) := by
  refine ⟨cat_period_iff, shuffle_period_iff, ?_, ?_, ?_, ?_⟩ <;> decide

end ErgodicCutoffCycleType
end Gnosis
