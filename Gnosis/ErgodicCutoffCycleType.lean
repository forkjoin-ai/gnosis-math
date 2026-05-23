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

-- ═══════════════════════════════════════════════════════════════════════
-- §0  Periods of a self-map over a carrier
-- ═══════════════════════════════════════════════════════════════════════

/-- `T` is a period of `f` over the carrier `c`: every carrier point returns. -/
def ReturnsAll {α : Type} (f : α → α) (c : List α) (T : Nat) : Prop :=
  ∀ x ∈ c, iter f T x = x

/-- Iteration is additive in the step count. -/
theorem iter_add {α : Type} (f : α → α) (a b : Nat) (x : α) :
    iter f (a + b) x = iter f a (iter f b x) := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ k ih =>
      rw [Nat.add_right_comm k 1 b]
      show f (iter f (k + b) x) = f (iter f k (iter f b x))
      rw [ih]

/-- If `x` returns after `p` steps, it returns after every multiple of `p`. -/
theorem iter_pmul_of_fix {α : Type} (f : α → α) (p : Nat) (x : α)
    (h : iter f p x = x) : ∀ q, iter f (p * q) x = x := by
  intro q
  induction q with
  | zero => rfl
  | succ k ih =>
      show iter f (p * k + p) x = x
      rw [iter_add, h, ih]

/-- A period is inherited by every multiple: `p ∣ T → period p → period T`. -/
theorem returnsAll_of_dvd {α : Type} (f : α → α) (c : List α) (p T : Nat)
    (hdvd : p ∣ T) (h : ReturnsAll f c p) : ReturnsAll f c T := by
  intro x hx
  rcases hdvd with ⟨q, rfl⟩
  exact iter_pmul_of_fix f p x (h x hx) q

/-- A carrier closed under `f` is closed under every iterate of `f`. -/
theorem iter_mem {α : Type} (f : α → α) (c : List α)
    (hclos : ∀ x ∈ c, f x ∈ c) (n : Nat) (x : α) (hx : x ∈ c) :
    iter f n x ∈ c := by
  induction n with
  | zero => exact hx
  | succ k ih => exact hclos (iter f k x) ih

/-- Membership helper: a positive `Nat` below 10 is one of `1..9`. -/
theorem mem_one_to_nine (r : Nat) (h0 : 0 < r) (h10 : r < 10) :
    r ∈ ([1,2,3,4,5,6,7,8,9] : List Nat) := by
  match r, h0, h10 with
  | 1, _, _ => decide
  | 2, _, _ => decide
  | 3, _, _ => decide
  | 4, _, _ => decide
  | 5, _, _ => decide
  | 6, _, _ => decide
  | 7, _, _ => decide
  | 8, _, _ => decide
  | 9, _, _ => decide
  | 0, h0, _ => exact (Nat.lt_irrefl 0 h0).elim
  | k + 10, _, h10 =>
      exact (Nat.lt_irrefl 10 (Nat.lt_of_le_of_lt (Nat.le_add_left 10 k) h10)).elim

/-- **Minimal period theorem.** If 10 is a period and no element of `1..9` is, then every
    period is a multiple of 10 — so 10 is the order of the cyclic group `f` generates. -/
theorem period_dvd_ten {α : Type} (f : α → α) (c : List α)
    (hclos : ∀ x ∈ c, f x ∈ c)
    (h10 : ReturnsAll f c 10)
    (hfail : ∀ d ∈ ([1,2,3,4,5,6,7,8,9] : List Nat), ¬ ReturnsAll f c d)
    (T : Nat) (hT : ReturnsAll f c T) : 10 ∣ T := by
  have hmod : 10 * (T / 10) + T % 10 = T := Nat.div_add_mod T 10
  have hmul : ReturnsAll f c (10 * (T / 10)) :=
    returnsAll_of_dvd f c 10 (10 * (T / 10)) ⟨T / 10, rfl⟩ h10
  have hr_ret : ReturnsAll f c (T % 10) := by
    intro x hx
    have hxT : iter f T x = x := hT x hx
    rw [← hmod, iter_add] at hxT
    have hmem : iter f (T % 10) x ∈ c := iter_mem f c hclos (T % 10) x hx
    rw [hmul (iter f (T % 10) x) hmem] at hxT
    exact hxT
  have hrlt : T % 10 < 10 := Nat.mod_lt T (by decide)
  rcases Nat.eq_zero_or_pos (T % 10) with hr0 | hrpos
  · refine ⟨T / 10, ?_⟩
    rw [hr0, Nat.add_zero] at hmod
    exact hmod.symm
  · exact absurd hr_ret (hfail (T % 10) (mem_one_to_nine (T % 10) hrpos hrlt))

-- ═══════════════════════════════════════════════════════════════════════
-- §1  Cycle-type fingerprint (conjugacy invariant)
-- ═══════════════════════════════════════════════════════════════════════

/-- Number of carrier points fixed by `f^d`. Across all `d`, this multiset of counts is
    a conjugacy invariant: conjugate permutations share it. -/
def countFixedBy {α : Type} [DecidableEq α] (f : α → α) (c : List α) (d : Nat) : Nat :=
  (c.filter (fun x => decide (iter f d x = x))).length

-- ═══════════════════════════════════════════════════════════════════════
-- §2  The cat map — order exactly 10, cycle type 1+2+2+10+10
-- ═══════════════════════════════════════════════════════════════════════

theorem cat_carrier_closed : ∀ p ∈ catCarrier, aeonCatMap p ∈ catCarrier := by decide

theorem cat_returns_all_10 : ReturnsAll aeonCatMap catCarrier 10 := by
  unfold ReturnsAll; decide

theorem cat_no_small_period :
    ∀ d ∈ ([1,2,3,4,5,6,7,8,9] : List Nat), ¬ ReturnsAll aeonCatMap catCarrier d := by
  unfold ReturnsAll; decide

/-- The periods of the cat map are exactly the multiples of 10 — order exactly 10. -/
theorem cat_period_iff (T : Nat) :
    ReturnsAll aeonCatMap catCarrier T ↔ 10 ∣ T := by
  constructor
  · exact period_dvd_ten aeonCatMap catCarrier cat_carrier_closed
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
    ∀ d ∈ ([1,2,3,4,5,6,7,8,9] : List Nat), ¬ ReturnsAll outShuffle12 shuffleCarrier d := by
  unfold ReturnsAll; decide

/-- The periods of the out-shuffle are exactly the multiples of 10 — order exactly 10. -/
theorem shuffle_period_iff (T : Nat) :
    ReturnsAll outShuffle12 shuffleCarrier T ↔ 10 ∣ T := by
  constructor
  · exact period_dvd_ten outShuffle12 shuffleCarrier shuffle_carrier_closed
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
