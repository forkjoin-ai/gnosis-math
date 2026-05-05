import Init
import Gnosis.Void.VoidWalking

namespace Gnosis

/-!
# Buleyean Probability: Frequentist Theory on Complement Sets
-/

-- ═══════════════════════════════════════════════════════════════════════
-- The Buleyean Sample Space
-- ═══════════════════════════════════════════════════════════════════════

/-- A Buleyean sample space: a finite set of choices with a void
    boundary tracking rejection counts. -/
structure BuleyeanSpace where
  /-- Number of choices in the sample space -/
  numChoices : Nat
  /-- At least 2 choices (nontrivial) -/
  nontrivial : 2 ≤ numChoices
  /-- Total observation rounds -/
  rounds : Nat
  /-- At least one round (we have observed something) -/
  positiveRounds : 0 < rounds
  /-- Rejection count per choice (the void boundary) -/
  voidBoundary : Fin numChoices → Nat
  /-- Each rejection count bounded by total rounds -/
  bounded : ∀ i, voidBoundary i ≤ rounds

/-- The complement weight of choice i: how many rounds it was
    NOT rejected, plus 1 (ensuring strict positivity). -/
def BuleyeanSpace.weight (bs : BuleyeanSpace) (i : Fin bs.numChoices) : Nat :=
  bs.rounds - Nat.min (bs.voidBoundary i) bs.rounds + 1

-- ═══════════════════════════════════════════════════════════════════════
-- Axiom 1: Non-negativity (strict positivity)
-- ═══════════════════════════════════════════════════════════════════════

/-- Buleyean Axiom 1: every choice has strictly positive weight. -/
theorem buleyean_positivity (bs : BuleyeanSpace) (i : Fin bs.numChoices) :
    0 < bs.weight i := by
  unfold BuleyeanSpace.weight
  exact Nat.succ_pos _

-- ═══════════════════════════════════════════════════════════════════════
-- Axiom 3: Monotone updating
-- ═══════════════════════════════════════════════════════════════════════

/-- Buleyean Axiom 3: a rejection cannot decrease any non-rejected
    choice's weight. -/
theorem buleyean_monotone_nonrejected
    (bu_rounds : Nat)
    (bu_voidBoundary_before : Fin n → Nat)
    (bu_voidBoundary_after : Fin n → Nat)
    (_rejected : Fin n)
    (i : Fin n) (_hNotRejected : i ≠ _rejected)
    (h_others : bu_voidBoundary_after i = bu_voidBoundary_before i) :
    (bu_rounds - Nat.min (bu_voidBoundary_before i) bu_rounds + 1) ≤
    (bu_rounds + 1 - Nat.min (bu_voidBoundary_after i) (bu_rounds + 1) + 1) := by
  rw [h_others]
  -- Convert Nat.min to generic min so Nat.min_eq_left/right rewrites apply
  show bu_rounds - min (bu_voidBoundary_before i) bu_rounds + 1 ≤
       bu_rounds + 1 - min (bu_voidBoundary_before i) (bu_rounds + 1) + 1
  -- Reduce to: R - min b R ≤ (R+1) - min b (R+1)
  refine Nat.add_le_add_right ?_ 1
  -- Case split on b ≤ R vs R ≤ b
  rcases Nat.le_total (bu_voidBoundary_before i) bu_rounds with hbR | hRb
  · -- Case b ≤ R: min b R = b, and b ≤ R ≤ R+1 so min b (R+1) = b
    have hbR1 : bu_voidBoundary_before i ≤ bu_rounds + 1 :=
      Nat.le_trans hbR (Nat.le_succ bu_rounds)
    rw [Nat.min_eq_left hbR, Nat.min_eq_left hbR1]
    -- Goal: R - b ≤ (R+1) - b
    exact Nat.sub_le_sub_right (Nat.le_succ bu_rounds) (bu_voidBoundary_before i)
  · -- Case R ≤ b: min b R = R, so LHS = R - R = 0
    rw [Nat.min_eq_right hRb]
    rw [Nat.sub_self]
    exact Nat.zero_le _

end Gnosis
