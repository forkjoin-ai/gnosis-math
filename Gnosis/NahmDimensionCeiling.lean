import Gnosis.SuperstringDimensionDerivation
import Gnosis.CostAlgebraDimensionNoGo

/-!
# Nahm Dimension Ceiling — closing the 10 ≤ d ≤ 11 sandwich

The cost-algebra `DimensionNoGo` proves the *floor*: every axis set
satisfying the cost-algebra constraints has dimension ≥ 10. Werner
Nahm's 1978 result on supergravity provides the *ceiling*: a
consistent supergravity theory has dimension ≤ 11, because higher
dimensions force the supersymmetry algebra to require massless
particles of spin > 2 (which are generally considered unphysical
above d = 11).

This module formalizes the Nahm ceiling structurally:

> If the cost-algebra carrier is at the **Nahm-minimal** regime —
> each axis at its forced cardinality, the gauge axis ≤ 1, and no
> doubled-Octagon (no E8 × E8 internal structure) — then the
> dimension is at most 11.

Combined with the floor `cost_algebra_dimension_at_least_ten`, this
gives the sandwich:

```
10 ≤ dim_cost_algebra ≤ 11   in the Nahm-minimal regime
```

The two values 10 and 11 are precisely the superstring critical
dimension and the M-theory dimension. Bosonic 26 is explicitly
outside the Nahm regime (it has the doubled-Octagon, breaks the
ceiling). The cost-algebra and supergravity together select the
unified-theory dimension uniquely.

## Honest framing

The Nahm bound itself is a physics result (Nahm 1978; reviewed in
de Wit, Smith 1986) about the maximum spacetime dimension for which
a consistent supergravity multiplet exists. We do not re-derive
Nahm's argument inside the cost-algebra; we *encode* the Nahm
ceiling as a structural constraint (`NahmMinimalAxisSet`) on the
axis decomposition, then prove the dimensional consequence.

The bosonic-string 26 is not excluded by the cost-algebra — it sits
at a valid tower wall. It is excluded by the *Nahm* constraint
because bosonic string theory has no supersymmetry and its
doubled-Octagon doesn't fit the supergravity multiplet.

Imports `Gnosis.SuperstringDimensionDerivation` and
`Gnosis.CostAlgebraDimensionNoGo`. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace NahmDimensionCeiling

open Gnosis.CostAlgebraDimensionNoGo
  (CostAlgebraAxisSet axisSetTotal cost_algebra_dimension_at_least_ten
   minimalSuperstringAxisSet minimalMTheoryAxisSet
   minimal_superstring_axis_set_is_ten
   minimal_m_theory_axis_set_is_eleven)

/-! ## The Nahm-minimal regime -/

/-- An axis set is **Nahm-minimal** if each axis sits at its forced
minimum cardinality and the gauge orientation is at most one (no
spin > 2 multiplets) and there is no doubled-Octagon (no E8 × E8
internal Cartan structure). The Nahm regime captures *consistent
supergravity* in the cost-algebra. -/
structure NahmMinimal (a : CostAlgebraAxisSet) : Prop where
  /-- Bule faces at the cyclePermute minimum of 3. -/
  bule_exact : a.buleFaces = 3
  /-- Bi-sided at the breathing-identity minimum of 2. -/
  bisided_exact : a.biSided = 2
  /-- Temporal at the second-degree-diff minimum of 3. -/
  temporal_exact : a.temporal = 3
  /-- Gauge orientation 0 or 1 (no higher-spin multiplets). -/
  gauge_at_most_one : a.gauge ≤ 1
  /-- No internal Cartan (heterotic 16-dim doesn't fit supergravity). -/
  doubled_octagon_zero : a.doubledOctagon = 0

/-! ## The Nahm ceiling -/

/-- **Nahm ceiling**: every Nahm-minimal axis set has dimension ≤ 11. -/
theorem nahm_dimension_at_most_eleven
    (a : CostAlgebraAxisSet) (h : NahmMinimal a) :
    axisSetTotal a ≤ 11 := by
  unfold axisSetTotal
  rw [h.bule_exact, h.bisided_exact, h.temporal_exact,
      a.vacuum_exactly_one, a.clinamen_exactly_one,
      h.doubled_octagon_zero]
  -- Goal: 3 + 2 + 3 + 1 + 1 + a.gauge + 0 ≤ 11
  have hg : a.gauge ≤ 1 := h.gauge_at_most_one
  omega

/-! ## The sandwich: 10 ≤ d ≤ 11 -/

/-- **The dimension sandwich**: every Nahm-minimal axis set has
dimension between 10 (the cost-algebra floor) and 11 (the Nahm
ceiling). The two integers in this range are precisely the
superstring (10) and M-theory (11) dimensions. -/
theorem nahm_dimension_sandwich
    (a : CostAlgebraAxisSet) (h : NahmMinimal a) :
    10 ≤ axisSetTotal a ∧ axisSetTotal a ≤ 11 :=
  ⟨cost_algebra_dimension_at_least_ten a,
   nahm_dimension_at_most_eleven a h⟩

/-- **Both endpoints achieved**: the superstring (10) and M-theory
(11) axis sets sit in the Nahm-minimal regime; their dimensions are
exactly the two integers in the sandwich. -/
theorem superstring_is_nahm_minimal :
    NahmMinimal minimalSuperstringAxisSet :=
  { bule_exact := rfl
    bisided_exact := rfl
    temporal_exact := rfl
    gauge_at_most_one := by decide
    doubled_octagon_zero := rfl }

theorem m_theory_is_nahm_minimal :
    NahmMinimal minimalMTheoryAxisSet :=
  { bule_exact := rfl
    bisided_exact := rfl
    temporal_exact := rfl
    gauge_at_most_one := by decide
    doubled_octagon_zero := rfl }

/-! ## Only 10 and 11 inhabit the Nahm sandwich

A Nahm-minimal axis set has dimension exactly 10 (gauge = 0) or
exactly 11 (gauge = 1). No other values are admissible. -/

theorem nahm_dimension_exactly_ten_or_eleven
    (a : CostAlgebraAxisSet) (h : NahmMinimal a) :
    axisSetTotal a = 10 ∨ axisSetTotal a = 11 := by
  unfold axisSetTotal
  rw [h.bule_exact, h.bisided_exact, h.temporal_exact,
      a.vacuum_exactly_one, a.clinamen_exactly_one,
      h.doubled_octagon_zero]
  -- Goal: 3 + 2 + 3 + 1 + 1 + a.gauge + 0 = 10 ∨ ... = 11
  -- Which simplifies to: 10 + a.gauge = 10 ∨ 10 + a.gauge = 11
  have hg : a.gauge ≤ 1 := h.gauge_at_most_one
  -- a.gauge is 0 or 1
  match hcases : a.gauge with
  | 0 => left; omega
  | 1 => right; omega
  | n + 2 => exfalso; omega

/-- The dimension is exactly 10 iff the gauge axis is zero. -/
theorem nahm_ten_iff_no_gauge
    (a : CostAlgebraAxisSet) (h : NahmMinimal a) :
    axisSetTotal a = 10 ↔ a.gauge = 0 := by
  unfold axisSetTotal
  rw [h.bule_exact, h.bisided_exact, h.temporal_exact,
      a.vacuum_exactly_one, a.clinamen_exactly_one,
      h.doubled_octagon_zero]
  have hg : a.gauge ≤ 1 := h.gauge_at_most_one
  constructor
  · intro hSum; omega
  · intro hg0; omega

/-- The dimension is exactly 11 iff the gauge axis is one. -/
theorem nahm_eleven_iff_gauge_one
    (a : CostAlgebraAxisSet) (h : NahmMinimal a) :
    axisSetTotal a = 11 ↔ a.gauge = 1 := by
  unfold axisSetTotal
  rw [h.bule_exact, h.bisided_exact, h.temporal_exact,
      a.vacuum_exactly_one, a.clinamen_exactly_one,
      h.doubled_octagon_zero]
  have hg : a.gauge ≤ 1 := h.gauge_at_most_one
  constructor
  · intro hSum; omega
  · intro hg1; omega

/-! ## Bosonic string explicitly outside the Nahm regime -/

open Gnosis.CostAlgebraDimensionNoGo (minimalBosonicStringAxisSet)

/-- The bosonic-string axis set has `doubledOctagon = 16`, so it
fails `NahmMinimal.doubled_octagon_zero`. Bosonic string theory's
26 dimensions are excluded from the Nahm sandwich exactly because
bosonic string has no supergravity. -/
theorem bosonic_string_not_nahm_minimal :
    ¬ NahmMinimal minimalBosonicStringAxisSet := by
  intro h
  have : minimalBosonicStringAxisSet.doubledOctagon = 0 := h.doubled_octagon_zero
  -- But the bosonic axis set has doubledOctagon = 16, contradiction
  unfold minimalBosonicStringAxisSet at this
  exact absurd this (by decide)

/-! ## Master theorem: the unified-theory dimension selection -/

/-- **The cost-algebra and Nahm constraints together select exactly
two dimensions: 10 and 11.** Floor (cost-algebra): dim ≥ 10. Ceiling
(Nahm sugra): dim ≤ 11 in the supergravity regime. The two values in
that range are precisely the superstring critical dimension (10) and
the M-theory dimension (11), each achieved by an explicit witness. -/
theorem unified_theory_dimension_selection_master :
    -- Floor: the cost-algebra forces dim ≥ 10
    (∀ a : CostAlgebraAxisSet, axisSetTotal a ≥ 10)
    -- Ceiling: Nahm-minimal regime forces dim ≤ 11
    ∧ (∀ a : CostAlgebraAxisSet, NahmMinimal a → axisSetTotal a ≤ 11)
    -- Only 10 or 11 inhabit the sandwich
    ∧ (∀ a : CostAlgebraAxisSet, NahmMinimal a →
        axisSetTotal a = 10 ∨ axisSetTotal a = 11)
    -- Both endpoints achieved
    ∧ (NahmMinimal minimalSuperstringAxisSet
        ∧ axisSetTotal minimalSuperstringAxisSet = 10)
    ∧ (NahmMinimal minimalMTheoryAxisSet
        ∧ axisSetTotal minimalMTheoryAxisSet = 11)
    -- Bosonic explicitly outside the Nahm regime
    ∧ ¬ NahmMinimal minimalBosonicStringAxisSet :=
  ⟨cost_algebra_dimension_at_least_ten,
   nahm_dimension_at_most_eleven,
   nahm_dimension_exactly_ten_or_eleven,
   ⟨superstring_is_nahm_minimal, minimal_superstring_axis_set_is_ten⟩,
   ⟨m_theory_is_nahm_minimal, minimal_m_theory_axis_set_is_eleven⟩,
   bosonic_string_not_nahm_minimal⟩

end NahmDimensionCeiling
end Gnosis
