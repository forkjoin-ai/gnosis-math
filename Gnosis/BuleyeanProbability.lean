import Init
import Gnosis.VoidWalking

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
  omega

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
    (_h_oneMore : True)
    (i : Fin n) (_hNotRejected : i ≠ _rejected)
    (h_others : bu_voidBoundary_after i = bu_voidBoundary_before i) :
    (bu_rounds - Nat.min (bu_voidBoundary_before i) bu_rounds + 1) ≤
    (bu_rounds + 1 - Nat.min (bu_voidBoundary_after i) (bu_rounds + 1) + 1) := by
  rw [h_others]
  simp [Nat.min_def]
  split <;> split <;> omega

end Gnosis
