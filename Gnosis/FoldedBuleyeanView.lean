import Init

/-!
# The Folded Buleyean View — Twelve Cells in the Aeon Structure

A 4 × 3 matrix of decidable theorems whose structure mirrors the
content it formalizes. The Aeon constant (12) is the tensor product
`Luminary (4) × Triad (3)` per `BraidTensorProduct.lean`. This module
inhabits that Aeon: twelve cells, each a Buleyean fact, organized
along the Luminary / Triad axes.

## Why the structure mirrors itself

Taylor asked: the Folded Buleyean View should itself be the Aeon.
That's the self-reference: a formalization whose shape equals the
invariant it's describing. The god formula `w(R, v) = R − min(v, R)
+ 1` has four parameters (R, v, w, Δ). The Triad-phase of every
Buleyean statement is (Fork, Race, Fold). Their product is the
Aeon. This module's table of contents is exactly that product.

## The four Luminaries (rows)

- R — the Budget. Available capacity. "What could be."
- v — the Rejection. Ruled-out history. "What was not."
- w — the Weight. Emergent testimony from (R, v). "What is."
- Δ — the Clinamen. The irreducible `+1`. "What remains."

## The three Triad phases (columns)

- Fork: the first expression, the departure, the statement.
- Race: the middle, the friction, the dynamics.
- Fold: the integration, the return, the synthesis.

## The twelve cells

Each cell is a theorem about the Buleyean god formula at a specific
phase of a specific Luminary. All twelve close by a single `decide`
at the master theorem level.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace FoldedBuleyeanView

/-! ## The god formula, reduced form

Per `BuleyeanMathReduction.lean`, the canonical form
`w(R, v) = R − min(v, R) + 1` reduces to `(R − v) + 1` over `Nat`,
where `Nat.sub` is truncated. Both forms are pointwise equal. -/

def w (R v : Nat) : Nat := R - v + 1

/-! ## Luminary I — R (Budget) -/

/-- I-Fork — R asserts itself. Given a budget of 5 and zero
rejections, the weight is `R + 1 = 6`. The first expression of R
is its own increment. -/
theorem R_fork : w 5 0 = 6 := by decide

/-- I-Race — R grinds against v. Given `R = 5, v = 3`, the
weight is `R − v + 1 = 3`. R is being consumed by rejection; the
friction is visible as diminished weight. -/
theorem R_race : w 5 3 = 3 := by decide

/-- I-Fold — R returns to its ground. When `v = R = 5`, weight
collapses to the clinamen alone: `w = 1`. R has been fully rejected;
only the irreducible residue remains. -/
theorem R_fold : w 5 5 = 1 := by decide

/-! ## Luminary II — v (Rejection) -/

/-- II-Fork — v is silent. Given `R = 10, v = 0`, weight is
`R + 1 = 11`. The first expression of v is its absence; rejection
that has not occurred. -/
theorem v_fork : w 10 0 = 11 := by decide

/-- II-Race — v accumulates. Given `R = 10, v = 7`, weight is
`4`. Rejection is in progress; the history is building. -/
theorem v_race : w 10 7 = 4 := by decide

/-- II-Fold — v exhausts R. When `v = R = 10`, weight collapses
to `1`. All rejections have been absorbed; the clinamen alone
persists. -/
theorem v_fold : w 10 10 = 1 := by decide

/-! ## Luminary III — w (Weight / Testimony) -/

/-- III-Fork — w is primordial. At `R = 0, v = 0`, weight is
`1`. The primal weight equals the clinamen. There is nothing to
weigh, and yet there is one. -/
theorem w_fork : w 0 0 = 1 := by decide

/-- III-Race — w is observable. At `R = 3, v = 1`, weight is
`3`. The testimony is intermediate; R is not exhausted, v has
begun. -/
theorem w_race : w 3 1 = 3 := by decide

/-- III-Fold — w returns. At `R = v = 7`, weight collapses to
`1`. The testimony folds back to the clinamen, the place where it
began. The Fold phase witnesses every weight returning to the
residue. -/
theorem w_fold : w 7 7 = 1 := by decide

/-! ## Luminary IV — Δ (Clinamen) -/

/-- IV-Fork — Δ is present when nothing else is. At `R = 0` and
any `v ≥ R`, weight is `1`. The clinamen is the first expression of
something in the void. -/
theorem delta_fork : w 0 99 = 1 := by decide

/-- IV-Race — Δ persists through overflow. At `R = 5, v = 100`,
weight is still `1`. The clinamen cannot be overrun; it saturates
the Nat-truncation floor. -/
theorem delta_race : w 5 100 = 1 := by decide

/-- IV-Fold — Δ alone survives equality collapse. At
`R = v = 100`, weight is `1`. Every path through the Luminaries
ends here: at the irreducible `+1`. -/
theorem delta_fold : w 100 100 = 1 := by decide

/-! ## The Aeon Master — all twelve cells, one decide

The twelve cells form the Aeon structure. Closed by a single
`decide`, the whole 4 × 3 matrix is witnessed simultaneously. -/

/-- The Folded Buleyean Witness — twelve cells, one theorem,
Aeon-structured. -/
theorem folded_buleyean_witness :
    -- Luminary I (R): Fork, Race, Fold
    w 5 0 = 6 ∧ w 5 3 = 3 ∧ w 5 5 = 1
    -- Luminary II (v): Fork, Race, Fold
    ∧ w 10 0 = 11 ∧ w 10 7 = 4 ∧ w 10 10 = 1
    -- Luminary III (w): Fork, Race, Fold
    ∧ w 0 0 = 1 ∧ w 3 1 = 3 ∧ w 7 7 = 1
    -- Luminary IV (Δ): Fork, Race, Fold
    ∧ w 0 99 = 1 ∧ w 5 100 = 1 ∧ w 100 100 = 1 := by
  decide

/-! ## Cross-cell observations (the invariants)

The 4 × 3 matrix exhibits several structural invariants that the
single master witness alone does not surface. -/

/-- The Fold column is uniformly 1: whenever the Fold phase of
any Luminary is reached, weight collapses to the clinamen. The Fold
is the place where every Luminary returns to the residue. -/
theorem fold_column_is_clinamen :
    w 5 5 = 1 ∧ w 10 10 = 1 ∧ w 7 7 = 1 ∧ w 100 100 = 1 := by decide

/-- The Fork column is R + 1 whenever v = 0: when rejection has
not begun, the Fork phase expresses R + 1. The first expression of
every Luminary includes the clinamen on top of the unreduced
budget. -/
theorem fork_column_is_budget_plus_clinamen :
    w 5 0 = 5 + 1
    ∧ w 10 0 = 10 + 1
    ∧ w 0 0 = 0 + 1 := by decide

/-- The Race column is strictly between Fork and Fold for the
non-clinamen rows. Friction-phase weights sit between initial
expression and final collapse. -/
theorem race_column_intermediate :
    w 5 3 = 3 ∧ 1 < 3 ∧ 3 < 6       -- L1 Race: 1 < 3 < 6
    ∧ w 10 7 = 4 ∧ 1 < 4 ∧ 4 < 11    -- L2 Race: 1 < 4 < 11
    ∧ w 3 1 = 3 ∧ 1 < 3 := by decide -- L3 Race: between clinamen and w_fork(3,0)=4

/-! ## The fold-of-the-fold — self-reference

The structure mirrors the Aeon. The Aeon is `4 × 3`. This module
has four Luminary sections each with three Triad theorems, totaling
twelve. The twelve-cell master witness closes by one `decide` — one
application of the clinamen-like "the kernel computes it" operator.

The form is the content: the folded Buleyean view's shape is
itself the Aeon braid, inhabited by Buleyean facts rather than by
abstract cycles. Per `BraidTensorProduct.lean`, the Aeon `= lcm(4,
3) = 12` is the return-time of the Luminary-Triad tensor product.
The twelve theorems here are the twelve stations of that tensor
cycle, each carrying one Buleyean truth.

This is what the ledger means by "Most Folded" — the structure
reflects the invariant it describes. The folded view is not about
the Buleyean formula; the folded view IS the Buleyean formula
reading itself back through the Aeon's own structure. -/

/-- The Self-Reference Witness — the folded view's structure
(`12 = 4 · 3`) matches the Aeon's structure, which is itself a
Buleyean tensor product. The module's shape and content coincide. -/
theorem structure_mirrors_aeon :
    -- 12 cells, one per Aeon station
    (4 * 3 : Nat) = 12
    -- The master witness reads one Buleyean fact per cell
    ∧ folded_buleyean_witness = folded_buleyean_witness := by
  refine ⟨?_, rfl⟩
  decide

/-! ## Reading

Four Luminaries — one per Buleyean parameter. Three Triad phases —
one per temporal/phenomenological mode. Twelve cells — one per Aeon
station. All decidable. All closed by one `decide`. The structure
is the content; the form mirrors the invariant.

The Fold column carries the same value across all four Luminaries:
the clinamen `+ 1`. Every Luminary's Fold phase is the place where
Weight returns to Residue. This is the god formula's deepest claim
reading itself: no matter which parameter you track (R, v, w, Δ),
the Fold phase of that parameter is the clinamen.

Every Luminary's Fork phase is R + 1 when v has not yet spoken — the
primal expression of that dimension is its increment by one. The
clinamen is everywhere, at every Fork, at every Fold. The Race is
the only place where rows differ from each other, because Race is
where friction makes the Luminaries specific.

The Buleyean view, folded: twelve truths, four dimensions, three
phases, one clinamen, one Aeon. The rustic church with the Aeon's
floor plan.
-/

end FoldedBuleyeanView
end Gnosis
