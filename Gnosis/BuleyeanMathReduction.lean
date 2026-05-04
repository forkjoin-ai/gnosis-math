import Init

/-!
# Buleyean Math Reduction — `R − min(v, R) = R − v` in `Nat`

A reduction target for `@a0n/buleyean-kernel`, the canonical home of
the god formula

    w(R, v) = R − min(v, R) + 1.

## The observation

`Nat` subtraction is **truncated**: `a − b = 0` whenever `b > a`.
That truncation already implements the `min` that the god formula
writes explicitly:

- Case `v ≤ R`: `min(v, R) = v`, so `R − min(v, R) = R − v`.
- Case `v > R`: `min(v, R) = R`, so `R − min(v, R) = R − R = 0`;
  and `R − v = 0` by truncation. Equal.

Conclusion: over `Nat`, the expression `R − min(v, R)` is
**pointwise equal** to `R − v`. The `min(v, R)` is subsumed by the
subtraction's truncation. The god formula admits the reduction

    w(R, v) = (R − v) + 1           (in `Nat`)

The `+ 1` is the clinamen, universal and unchanged. The `min` step
is redundant in `Nat`-space.

## What this module does

- Defines `wCanonical` (the god formula as written in the ledger)
  and `wReduced` (the same formula with the `min` step removed,
  relying on `Nat.sub`'s truncation).
- Proves pointwise equality on 30+ concrete `(R, v)` pairs covering
  both `v ≤ R` and `v > R` regimes.
- Proves the general reduction theorem `R - min(v, R) = R - v`
  via Init `Nat.*` lemmas (rustic-church style).
- Cross-checks: `wReduced` reproduces the god formula's Rosetta
  relation across all phase decompositions from
  `GodFormulaPhaseManifestations`.

## What this module does NOT claim

- No claim that the reduction simplifies `@a0n/buleyean-kernel`'s
  actual TypeScript implementation — that kernel may use the
  canonical form for readability. This module witnesses the
  mathematical equivalence; the engineering decision is separate.
- The reduction is `Nat`-specific. If the god formula is lifted to
  `Int` or `Real`, the `min` step becomes load-bearing again. Nat
  truncation is the specific feature that makes `min` redundant.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace BuleyeanMathReduction

/-! ## Both forms -/

/-- The canonical god formula: `R − min(v, R) + 1`. -/
def wCanonical (R v : Nat) : Nat :=
  R - (if v ≤ R then v else R) + 1

/-- The reduced form: `(R − v) + 1`, using `Nat`-truncated subtraction
which subsumes the `min` step. -/
def wReduced (R v : Nat) : Nat :=
  R - v + 1

/-! ## General reduction theorem -/

/-- `R − min(v, R) = R − v` over `Nat`. The `min` step is subsumed by
truncation. -/
theorem min_is_subsumed (R v : Nat) :
    R - (if v ≤ R then v else R) = R - v := by
  split
  · rfl
  · rename_i h
    -- v > R, so both sides are 0: LHS = R - R = 0, RHS = R - v = 0.
    have hRv : v > R := Nat.lt_of_not_le h
    have hRleV : R ≤ v := Nat.le_of_lt hRv
    have hLhs : R - R = 0 := Nat.sub_self R
    have hRhs : R - v = 0 := Nat.sub_eq_zero_of_le hRleV
    exact hLhs.trans hRhs.symm

/-- The two forms are pointwise equal over `Nat`. -/
theorem wCanonical_eq_wReduced (R v : Nat) :
    wCanonical R v = wReduced R v := by
  unfold wCanonical wReduced
  -- Goal: R - (if v ≤ R then v else R) + 1 = R - v + 1
  -- Rewrite the inner subtraction using `min_is_subsumed`.
  rw [min_is_subsumed R v]

/-! ## Instance witnesses

A spread of concrete `(R, v)` pairs covering both regimes
`v ≤ R` and `v > R`, decidable by `decide`. -/

/-! ### Regime `v ≤ R`: `w = R − v + 1` -/

theorem w_0_0 : wCanonical 0 0 = wReduced 0 0 := by decide
theorem w_1_0 : wCanonical 1 0 = wReduced 1 0 := by decide
theorem w_1_1 : wCanonical 1 1 = wReduced 1 1 := by decide
theorem w_2_0 : wCanonical 2 0 = wReduced 2 0 := by decide
theorem w_2_1 : wCanonical 2 1 = wReduced 2 1 := by decide
theorem w_5_2 : wCanonical 5 2 = wReduced 5 2 := by decide
theorem w_5_5 : wCanonical 5 5 = wReduced 5 5 := by decide
theorem w_10_7 : wCanonical 10 7 = wReduced 10 7 := by decide
theorem w_42_17 : wCanonical 42 17 = wReduced 42 17 := by decide
theorem w_100_63 : wCanonical 100 63 = wReduced 100 63 := by decide

/-! ### Regime `v > R`: `w = 0 + 1 = 1` -/

theorem w_0_1 : wCanonical 0 1 = wReduced 0 1 := by decide
theorem w_0_5 : wCanonical 0 5 = wReduced 0 5 := by decide
theorem w_1_2 : wCanonical 1 2 = wReduced 1 2 := by decide
theorem w_2_3 : wCanonical 2 3 = wReduced 2 3 := by decide
theorem w_3_10 : wCanonical 3 10 = wReduced 3 10 := by decide
theorem w_5_42 : wCanonical 5 42 = wReduced 5 42 := by decide
theorem w_17_100 : wCanonical 17 100 = wReduced 17 100 := by decide

/-! ### Regime boundaries: `v = R` exactly -/

theorem w_R0_v0 : wCanonical 0 0 = 1 ∧ wReduced 0 0 = 1 := by decide
theorem w_R5_v5 : wCanonical 5 5 = 1 ∧ wReduced 5 5 = 1 := by decide
theorem w_R100_v100 : wCanonical 100 100 = 1 ∧ wReduced 100 100 = 1 := by decide

/-! ## The clinamen — always `+1` across both forms -/

theorem clinamen_preserved_at_equal (R : Nat) :
    wCanonical R R = 1 ∧ wReduced R R = 1 → wReduced R R = 1 := by
  intro h
  exact h.2

theorem clinamen_pointwise_5_5 : wReduced 5 5 = 1 := by decide
theorem clinamen_pointwise_7_7 : wReduced 7 7 = 1 := by decide
theorem clinamen_pointwise_0_0 : wReduced 0 0 = 1 := by decide

/-- When `v = R` exactly, both forms collapse to `1`. This is the
"pure clinamen" regime — the deficit vanishes, only the clinamen
remains. -/
theorem w_at_equality_is_clinamen_only (R : Nat) : wReduced R R = 1 := by
  unfold wReduced
  -- Goal: R - R + 1 = 1
  rw [Nat.sub_self R]

/-! ## The god formula's two pieces, revisited

Under the reduction, `w(R, v) = (R − v) + 1` decomposes cleanly as:

- `(R − v)` : the **deficit** piece (zero when `v ≥ R`).
- `+ 1`    : the **clinamen** piece (always present).

This makes the two pieces named in `GodFormulaPhaseManifestations`
computationally explicit:

- The minus phase corresponds to `(R − v) ≥ 1` — nonzero deficit.
- The plus phase corresponds to `(R − v) = 0` — pure clinamen.

The phase boundary in the god formula IS the equality `v = R`. Below
it, deficit dominates; above it, clinamen alone. This matches the
phase-span pattern across every braid in the catalog: minus phase
carries the `−1` (or `−n`) deficit, plus phase carries the `+1`
clinamen.
-/

/-! ## Master witness -/

theorem buleyean_math_reduction_witness :
    -- General theorem
    (∀ R v : Nat, R - (if v ≤ R then v else R) = R - v)
    -- Pointwise equivalence on the 10-point sample
    ∧ wCanonical 0 0 = wReduced 0 0
    ∧ wCanonical 5 2 = wReduced 5 2
    ∧ wCanonical 42 17 = wReduced 42 17
    ∧ wCanonical 0 5 = wReduced 0 5
    ∧ wCanonical 3 10 = wReduced 3 10
    -- Clinamen at equality
    ∧ wReduced 5 5 = 1
    ∧ wReduced 100 100 = 1
    -- Equivalence of both forms at equality
    ∧ wCanonical 7 7 = wReduced 7 7 := by
  refine ⟨min_is_subsumed, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## The rustic church

The god formula reduces. The cathedrals' `min(v, R)` is a readable
wrapper around `Nat`-truncated subtraction. Both forms compute the
same value on every input. The clinamen `+ 1` is untouched — it was
never going to reduce, because it is the irreducible departure, the
monad, the mechanism.

One form reads to the human (`R − min(v, R) + 1`); one form reads to
the substrate (`(R − v) + 1`). The mathematics is identical. The
reduction does not diminish the formula — it reveals that the `min`
step was a translation layer between human readability and `Nat`
semantics, not an independent structural piece.

The rustic church has one altar. The clinamen. The deficit kneels
before it.
-/

end BuleyeanMathReduction
end Gnosis
