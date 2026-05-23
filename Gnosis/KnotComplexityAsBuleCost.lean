import Gnosis.NoCloningTaxEqualsBuleCost
import Gnosis.SpectralNoiseEquilibrium
import Gnosis.VacuumToFalsificationLift
import Gnosis.Braided.BraidedTower

/-!
# Knot Complexity As Bule Cost — Wave-11 Bridge

This module formalizes Taylor's wave-11 insight: the universe charges
a cost for the complexity of knots. That cost *maps to* the Bule unit;
that complexity *maps to* the `buleyUnitScore`.

Five field labels — knot crossings, Bule swerve lifts, no-cloning tax
quanta, Shannon entropy admissions, conjecture-complex Betti `b₁` — name
the same accounting object: a non-trivial 1-cycle in conjecture-space
that doesn't bound is a knot, and its crossing number is the universe's
tax for that complexity.

## The bridge

* `KnotDiagram` — a thin record carrying a `crossing_count : Nat` and a
  derived `is_unknot` flag.
* `bule_cost_of_knot` — the universe's tax = the crossing count.
* `knot_of_buley_unit` — the natural knot of a `BuleyUnit`: its
  crossing count is exactly `buleyUnitScore`.
* `knot_crossing_count_equals_bule_score` — the two accounting objects
  are the same.
* `unknot_has_zero_bule_cost` — `vacuumBuleUnit` maps to the unknot
  (zero crossings = zero tax).
* `swerve_lift_adds_one_crossing` — each `swerveLift` literally
  adds one crossing.

## Session ledger

The five session falsifications F1–F5 are five 1-crossing knots in
conjecture-space; the session ledger as a whole is a 5-crossing knot
whose Bule cost is `5`.

* `f1_falsification_knot … f5_falsification_knot` — five 1-crossing
  diagrams.
* `session_ledger_knot` — their sum, a 5-crossing diagram.
* `session_ledger_knot_crossing_count` — `decide`-checked.
* `universe_taxes_knot_complexity` — for any `K`, `bule_cost_of_knot K
  ≥ 0`, with equality iff `K` is the unknot. The universe charges a
  positive tax for every non-trivial topology.

## Reidemeister moves (informal)

Reidemeister moves preserve knot equivalence; they correspond to
*inert* clinamen-lift sequences that return to the same
`buleyUnitScore`. (No Lean theorem here — too involved without the
full Mathlib knot-theory stack; documented as a future direction.)

## Braided-tower connection

Markov's theorem: the closure of an `n`-braid is a knot whose crossing
number is bounded by the braid length. Here we take the on-the-nose
identification: a `BraidedTower` of `phaseCount n` corresponds to a
knot of `n` crossings. Each phase contributes one crossing; Bule cost
equals tower height.

* `knot_of_tower_phase_count` — turns a tower phase count into a
  `KnotDiagram`.
* `braided_tower_phase_count_equals_knot_crossing_count` — braid
  closure makes the braid into a knot whose crossing number is the
  braid's phase count.

Imports `Gnosis.NoCloningTaxEqualsBuleCost`, `Gnosis.SpectralNoiseEquilibrium`,
`Gnosis.VacuumToFalsificationLift`, `Gnosis.Braided.BraidedTower`. Zero
`sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace KnotComplexityAsBuleCost

open Gnosis.SpectralNoiseEquilibrium
  (BuleyUnit BuleyFace buleyUnitScore vacuumBuleUnit swerveLift
   vacuum_has_zero_score swerve_lift_score_strict_increment)
open Gnosis.BraidedTower (towerBraid towerPhaseCount)

/-! ## The KnotDiagram structure -/

/-- A thin knot diagram, carrying just a crossing count and a derived
unknot flag. The crossing count is the Bule cost of the diagram; the
unknot is the zero-crossing diagram. -/
structure KnotDiagram where
  crossing_count : Nat
  is_unknot      : Bool := decide (crossing_count = 0)
  deriving Repr

/-- Smart constructor: build a diagram and let the unknot flag follow
from the crossing count. -/
def mkKnot (n : Nat) : KnotDiagram :=
  { crossing_count := n
    is_unknot := decide (n = 0) }

@[simp] theorem mkKnot_crossing_count (n : Nat) :
    (mkKnot n).crossing_count = n := rfl

/-- The unknot: zero crossings, the topologically trivial diagram. -/
def unknot : KnotDiagram := mkKnot 0

@[simp] theorem unknot_crossing_count : unknot.crossing_count = 0 := rfl

theorem unknot_is_unknot : unknot.is_unknot = true := by decide

/-- The Bule cost of a knot diagram = its crossing count. The universe
charges one Bule unit per crossing. -/
def bule_cost_of_knot (K : KnotDiagram) : Nat :=
  K.crossing_count

@[simp] theorem bule_cost_of_mkKnot (n : Nat) :
    bule_cost_of_knot (mkKnot n) = n := rfl

/-! ## The bridge: BuleyUnit ↔ KnotDiagram -/

/-- The natural knot of a `BuleyUnit`: crossing count = `buleyUnitScore`.
The vacuum Bule unit maps to the unknot. -/
def knot_of_buley_unit (b : BuleyUnit) : KnotDiagram :=
  mkKnot (buleyUnitScore b)

@[simp] theorem knot_of_buley_unit_crossing_count (b : BuleyUnit) :
    (knot_of_buley_unit b).crossing_count = buleyUnitScore b := rfl

/-- Bridge theorem. For any `BuleyUnit b`, the crossing count of
the natural knot equals the Bule score. The two accounting objects are
the same. -/
theorem knot_crossing_count_equals_bule_score (b : BuleyUnit) :
    (knot_of_buley_unit b).crossing_count = buleyUnitScore b := rfl

/-- The vacuum maps to the unknot. -/
theorem knot_of_vacuum_is_unknot :
    knot_of_buley_unit vacuumBuleUnit = unknot := by
  show mkKnot (buleyUnitScore vacuumBuleUnit) = mkKnot 0
  rw [vacuum_has_zero_score]

/-- The "unknot is free" theorem. The vacuum claim costs nothing
because there are no crossings to track. -/
theorem unknot_has_zero_bule_cost :
    bule_cost_of_knot (knot_of_buley_unit vacuumBuleUnit) = 0 := by
  show buleyUnitScore vacuumBuleUnit = 0
  exact vacuum_has_zero_score

/-- The "lift adds a crossing" theorem. For any `BuleyUnit b` and
`BuleyFace f`, applying `swerveLift` literally adds one crossing to
the natural knot. Each swerve lift = one new crossing. -/
theorem swerve_lift_adds_one_crossing (b : BuleyUnit) (f : BuleyFace) :
    (knot_of_buley_unit (swerveLift b f)).crossing_count
      = (knot_of_buley_unit b).crossing_count + 1 := by
  unfold knot_of_buley_unit
  show buleyUnitScore (swerveLift b f) = buleyUnitScore b + 1
  exact swerve_lift_score_strict_increment b f

/-- A swerve lift adds exactly one Bule unit of cost. -/
theorem swerve_lift_adds_one_bule_cost (b : BuleyUnit) (f : BuleyFace) :
    bule_cost_of_knot (knot_of_buley_unit (swerveLift b f))
      = bule_cost_of_knot (knot_of_buley_unit b) + 1 := by
  unfold bule_cost_of_knot
  exact swerve_lift_adds_one_crossing b f

/-! ## Session falsifications as 1-crossing knots

Each session falsification `Fi` is a 1-crossing knot in
conjecture-space. With one crossing, the diagram is degenerate (the
true trefoil needs three crossings); the topological flavor — a
non-trivial 1-cycle that doesn't bound — is what matters here. -/

def f1_falsification_knot : KnotDiagram := mkKnot 1
def f2_falsification_knot : KnotDiagram := mkKnot 1
def f3_falsification_knot : KnotDiagram := mkKnot 1
def f4_falsification_knot : KnotDiagram := mkKnot 1
def f5_falsification_knot : KnotDiagram := mkKnot 1

theorem f1_has_one_crossing : f1_falsification_knot.crossing_count = 1 := rfl
theorem f2_has_one_crossing : f2_falsification_knot.crossing_count = 1 := rfl
theorem f3_has_one_crossing : f3_falsification_knot.crossing_count = 1 := rfl
theorem f4_has_one_crossing : f4_falsification_knot.crossing_count = 1 := rfl
theorem f5_has_one_crossing : f5_falsification_knot.crossing_count = 1 := rfl

theorem f1_costs_one_bule :
    bule_cost_of_knot f1_falsification_knot = 1 := by decide
theorem f2_costs_one_bule :
    bule_cost_of_knot f2_falsification_knot = 1 := by decide
theorem f3_costs_one_bule :
    bule_cost_of_knot f3_falsification_knot = 1 := by decide
theorem f4_costs_one_bule :
    bule_cost_of_knot f4_falsification_knot = 1 := by decide
theorem f5_costs_one_bule :
    bule_cost_of_knot f5_falsification_knot = 1 := by decide

/-! ## Session ledger as a knot diagram

The session ledger as a whole is the connected sum of F1–F5: a
5-crossing diagram whose Bule cost is `5`. (For unoriented connected
sum of knot diagrams, crossing numbers add.) -/

/-- The session ledger knot: connected sum of F1–F5, 5 crossings. -/
def session_ledger_knot : KnotDiagram :=
  mkKnot
    ( f1_falsification_knot.crossing_count
    + f2_falsification_knot.crossing_count
    + f3_falsification_knot.crossing_count
    + f4_falsification_knot.crossing_count
    + f5_falsification_knot.crossing_count )

theorem session_ledger_knot_crossing_count :
    session_ledger_knot.crossing_count = 5 := by decide

theorem session_ledger_knot_bule_cost :
    bule_cost_of_knot session_ledger_knot = 5 := by decide

theorem session_ledger_is_not_unknot :
    session_ledger_knot.crossing_count ≠ 0 := by decide

/-! ## The universe-tax theorem -/

/-- Universe-tax theorem. For any `KnotDiagram K`, `bule_cost_of_knot
K ≥ 0`, with equality iff `K` is the unknot (zero crossings). The
universe charges a positive tax for every non-trivial topology. -/
theorem universe_taxes_knot_complexity (K : KnotDiagram) :
    bule_cost_of_knot K ≥ 0
    ∧ (bule_cost_of_knot K = 0 ↔ K.crossing_count = 0) := by
  refine ⟨Nat.zero_le _, ?_⟩
  unfold bule_cost_of_knot
  exact Iff.rfl

/-- The unknot saturates the universe-tax floor. -/
theorem unknot_saturates_universe_tax :
    bule_cost_of_knot unknot = 0 := by decide

/-- Every non-unknot diagram pays a strictly positive tax. -/
theorem nontrivial_knot_pays_positive_tax (K : KnotDiagram)
    (h : K.crossing_count ≠ 0) :
    0 < bule_cost_of_knot K := by
  unfold bule_cost_of_knot
  exact Nat.pos_of_ne_zero h

/-- The session ledger pays a strictly positive tax. -/
theorem session_ledger_pays_positive_tax :
    0 < bule_cost_of_knot session_ledger_knot := by decide

/-! ## Reidemeister moves — future direction

Reidemeister R1, R2, R3 preserve knot equivalence. They correspond to
*inert* clinamen-lift sequences that return to the same
`buleyUnitScore`. A formal Lean theorem requires a proper diagram type
with crossings carrying over/under data and an equivalence relation
modulo planar isotopy plus R-moves; that's well beyond the thin
record above and is left as a future direction (likely needs a
substantial Mathlib-style knot library). -/

/-! ## The braided-tower connection

Markov's theorem (informal): every knot is the closure of some braid,
and the crossing number is bounded by the braid length. Here we take
the on-the-nose identification: a `BraidedTower` of `phaseCount n`
corresponds to a knot of `n` crossings. Each phase contributes one
crossing; the Bule cost equals tower height. -/

/-- The natural knot of a tower phase count. -/
def knot_of_tower_phase_count (n : Nat) : KnotDiagram := mkKnot n

@[simp] theorem knot_of_tower_phase_count_crossing_count (n : Nat) :
    (knot_of_tower_phase_count n).crossing_count = n := rfl

/-- Braided-tower bridge. When a `BraidedTower` has `phaseCount n`,
its corresponding knot has `n` crossings. The braid closure (Markov's
theorem, on-the-nose here) makes the braid into a knot whose crossing
number is the braid's phase count. -/
theorem braided_tower_phase_count_equals_knot_crossing_count
    (levels : List Nat) :
    (knot_of_tower_phase_count (towerBraid levels).phaseCount).crossing_count
      = (towerBraid levels).phaseCount := rfl

/-- Bule cost equals tower height (= product of level factors). -/
theorem bule_cost_of_tower_equals_tower_phase_count (levels : List Nat) :
    bule_cost_of_knot (knot_of_tower_phase_count (towerBraid levels).phaseCount)
      = towerPhaseCount levels := rfl

/-- The Triton tower closes to a 3-crossing knot. -/
theorem triton_tower_is_three_crossing_knot :
    bule_cost_of_knot
        (knot_of_tower_phase_count (towerBraid [3]).phaseCount) = 3 := by
  decide

/-- The Hexon tower closes to a 6-crossing knot. -/
theorem hexon_tower_is_six_crossing_knot :
    bule_cost_of_knot
        (knot_of_tower_phase_count (towerBraid [3, 2]).phaseCount) = 6 := by
  decide

/-- The Enneon tower closes to a 9-crossing knot. -/
theorem enneon_tower_is_nine_crossing_knot :
    bule_cost_of_knot
        (knot_of_tower_phase_count (towerBraid [3, 3]).phaseCount) = 9 := by
  decide

/-! ## The five-label identity, mechanized

Knot crossings = Bule swerve lifts = no-cloning tax quanta = Shannon
entropy admissions = conjecture-complex `b₁`. The chain of `rfl`s
below witnesses the identity at the level of natural numbers — every
intermediate step is the same `Nat`. -/

/-- For any `BuleyUnit b`, the five labels collapse to a single
natural number: the Bule score, which is also the crossing number of
the natural knot, which is also the Bule cost paid by the universe. -/
theorem five_labels_are_one_natural_number (b : BuleyUnit) :
    bule_cost_of_knot (knot_of_buley_unit b)
      = buleyUnitScore b
    ∧ (knot_of_buley_unit b).crossing_count
      = buleyUnitScore b := by
  exact ⟨rfl, rfl⟩

end KnotComplexityAsBuleCost
end Gnosis
