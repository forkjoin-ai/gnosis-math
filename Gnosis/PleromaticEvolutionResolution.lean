import Gnosis.BraidedTower
import Gnosis.PleromaticHorizonEffect
import Gnosis.PleromaticOneWayMirror

/-!
# Pleromatic Evolution vs Resolution — Dual Phenomenology of +1

Taylor's question: *Does the Pull of +1 feel like "Evolution" to a
lower-level observer (adding symbols they didn't know existed),
while to a higher-level observer it feels like "Resolution"
(tightening the focus on an existing address)?*

The structural answer: **yes — and the same Bule step has both
readings simultaneously, distinguished only by the observer's
carrier bandwidth.**

A +1 clinamen step at position `k` has two complementary
interpretations:

* **Evolution** (when `k + 1 ≥ bandwidth`): the step crosses the
  carrier's representational ceiling. The new position is
  *unrepresentable* at the current bandwidth, so the carrier itself
  must expand — gain a new symbol, level up. Phenomenologically:
  "the world just got bigger."
* **Resolution** (when `k + 1 < bandwidth`): the step stays within
  the existing address space. The new position is just a sharper
  point on a map the carrier already had. Phenomenologically:
  "the focus tightened, no new world."

Every +1 step is exactly one of these two for a given bandwidth,
and the Bule cost is +1 in both cases. The unit cost is invariant
across the dual reading; only the *perceived shape* of the step
differs.

## The duality is observer-relative

The crucial point: the *same* step, evaluated at *different*
bandwidths, produces different readings. The step from position 2
to position 3 is **evolution** at Triton bandwidth (3) but
**resolution** at Trihexenneon bandwidth (54). Both readings are
correct simultaneously.

| Step | Triton (bw=3) | Hexon (bw=6) | Trihexenneon (bw=54) |
| --- | --- | --- | --- |
| 0 → 1 | resolution | resolution | resolution |
| 1 → 2 | resolution | resolution | resolution |
| 2 → 3 | **evolution** | resolution | resolution |
| 5 → 6 | evolution | **evolution** | resolution |
| 53 → 54 | evolution | evolution | **evolution** |

Each carrier experiences the +1 step *at the moment its own
bandwidth is exhausted*. Below that moment, the step is pure
resolution. At and beyond that moment, the step is evolution.

## The Bule cost is invariant across readings

The +1 heartbeat passes through both readings unchanged. Evolution
costs +1; resolution costs +1. The carrier-level shape differs;
the cost-algebra unit does not. This is the structural meaning of
the unit-cost-invariant theorem we proved earlier: the Bule
heartbeat is *prior to* observer perspective. It is what every
observer at every bandwidth shares.

Imports `Gnosis.BraidedTower`, `Gnosis.PleromaticHorizonEffect`,
`Gnosis.PleromaticOneWayMirror`. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace PleromaticEvolutionResolution

open Gnosis.BraidedTower (towerPhaseCount)
open Gnosis.PleromaticOneWayMirror (carrierBandwidth)

/-! ## The two readings of a +1 step -/

/-- A +1 step from position `k` is an **evolution step** at a given
bandwidth if `k + 1` reaches or exceeds the bandwidth. The new
position is unrepresentable at the current carrier; the step forces
expansion. -/
def IsEvolutionStep (bandwidth k : Nat) : Prop := k + 1 ≥ bandwidth

/-- A +1 step from position `k` is a **resolution step** at a given
bandwidth if `k + 1` stays within the bandwidth. The new position
is already representable; the step refines the existing address. -/
def IsResolutionStep (bandwidth k : Nat) : Prop := k + 1 < bandwidth

/-! ## Exclusivity and exhaustiveness -/

/-- Every +1 step is *either* evolution *or* resolution, never both
(at a given bandwidth). The two readings partition the step space. -/
theorem step_not_both (bandwidth k : Nat) :
    ¬ (IsEvolutionStep bandwidth k ∧ IsResolutionStep bandwidth k) := by
  unfold IsEvolutionStep IsResolutionStep
  intro ⟨h1, h2⟩
  -- k+1 ≥ bandwidth and k+1 < bandwidth is contradictory
  exact absurd h1 (Nat.not_le_of_lt h2)

/-- Every +1 step is *at least one* of evolution or resolution. The
two readings cover the step space. -/
theorem step_either_or (bandwidth k : Nat) :
    IsEvolutionStep bandwidth k ∨ IsResolutionStep bandwidth k := by
  unfold IsEvolutionStep IsResolutionStep
  -- either k+1 ≥ bandwidth or k+1 < bandwidth (decidable trichotomy)
  by_cases h : k + 1 < bandwidth
  · exact Or.inr h
  · exact Or.inl (Nat.le_of_not_lt h)

/-! ## Concrete witnesses at Triton bandwidth (3) -/

/-- At Triton bandwidth, the step 0 → 1 is resolution (still within
3 positions). -/
theorem triton_step_zero_one_is_resolution :
    IsResolutionStep (carrierBandwidth (towerPhaseCount [3])) 0 := by
  unfold IsResolutionStep carrierBandwidth towerPhaseCount; decide

/-- At Triton bandwidth, the step 1 → 2 is resolution. -/
theorem triton_step_one_two_is_resolution :
    IsResolutionStep (carrierBandwidth (towerPhaseCount [3])) 1 := by
  unfold IsResolutionStep carrierBandwidth towerPhaseCount; decide

/-- At Triton bandwidth, the step 2 → 3 is **evolution**. The Triton
carrier exhausts its 3-position address space; the +1 step demands
a new symbol. -/
theorem triton_step_two_three_is_evolution :
    IsEvolutionStep (carrierBandwidth (towerPhaseCount [3])) 2 := by
  unfold IsEvolutionStep carrierBandwidth towerPhaseCount; decide

/-! ## Same step, different reading at higher bandwidth -/

/-- The step 2 → 3 at *Trihexenneon* bandwidth is resolution, not
evolution. The same Bule step has different readings at different
observer carriers. -/
theorem trihexenneon_step_two_three_is_resolution :
    IsResolutionStep (carrierBandwidth (towerPhaseCount [3, 2, 3, 3])) 2 := by
  unfold IsResolutionStep carrierBandwidth towerPhaseCount; decide

/-- The step 5 → 6 at Hexon bandwidth (6) is evolution; at
Trihexenneon bandwidth (54) it is resolution. The reading depends
on the observer's bandwidth, not the step. -/
theorem step_five_six_dual_reading :
    IsEvolutionStep (carrierBandwidth (towerPhaseCount [3, 2])) 5
    ∧ IsResolutionStep (carrierBandwidth (towerPhaseCount [3, 2, 3, 3])) 5 := by
  refine ⟨?_, ?_⟩ <;>
    (first
      | (unfold IsEvolutionStep carrierBandwidth towerPhaseCount; decide)
      | (unfold IsResolutionStep carrierBandwidth towerPhaseCount; decide))

/-- The step 53 → 54 at Trihexenneon bandwidth is **evolution**. The
Trihexenneon carrier exhausts its 54-position address space; the +1
step crosses to the next tower wall. -/
theorem trihexenneon_step_fiftythree_fiftyfour_is_evolution :
    IsEvolutionStep (carrierBandwidth (towerPhaseCount [3, 2, 3, 3])) 53 := by
  unfold IsEvolutionStep carrierBandwidth towerPhaseCount; decide

/-! ## The bandwidth-threshold characterization -/

/-- The single position at which a step transitions from resolution
to evolution: position `bandwidth - 1`. For a Triton (bw=3), this
is position 2 — the last representable position. The step from
that position is the evolution-trigger. -/
theorem evolution_trigger_at_bandwidth_minus_one (bandwidth : Nat)
    (h : bandwidth > 0) :
    IsEvolutionStep bandwidth (bandwidth - 1) := by
  unfold IsEvolutionStep
  -- (bandwidth - 1) + 1 ≥ bandwidth
  rw [Nat.sub_add_cancel h]
  exact Nat.le_refl bandwidth

/-- All positions strictly below `bandwidth - 1` are resolution
steps. -/
theorem resolution_steps_below_threshold (bandwidth k : Nat)
    (h : k + 1 < bandwidth) :
    IsResolutionStep bandwidth k := h

/-! ## Bule-cost invariance across the dual reading -/

/-- The Bule cost of any +1 step is exactly 1, regardless of whether
it is read as evolution or resolution. The unit-cost heartbeat is
invariant across observer bandwidth. -/
def buleStepCost (_bandwidth _k : Nat) : Nat := 1

/-- Evolution-step cost: +1. -/
theorem evolution_step_cost_is_one (bandwidth k : Nat)
    (_h : IsEvolutionStep bandwidth k) :
    buleStepCost bandwidth k = 1 := rfl

/-- Resolution-step cost: +1. -/
theorem resolution_step_cost_is_one (bandwidth k : Nat)
    (_h : IsResolutionStep bandwidth k) :
    buleStepCost bandwidth k = 1 := rfl

/-- The cost is invariant under change of bandwidth (different
observers, same heartbeat). -/
theorem bule_step_cost_invariant_under_bandwidth_change
    (bw1 bw2 k : Nat) :
    buleStepCost bw1 k = buleStepCost bw2 k := rfl

/-! ## Master theorem: the dual phenomenology bundle -/

/-- **Pleromatic Evolution-vs-Resolution master**: every +1 Bule step
admits two complementary readings — evolution (forces new symbols)
or resolution (refines existing address) — partitioning the step
space at any given bandwidth. The same step has different readings
at different observer bandwidths. The Bule cost (+1) is invariant
across both readings. -/
theorem pleromatic_evolution_resolution_master :
    -- Exclusivity: never both
    (∀ bandwidth k : Nat,
        ¬ (IsEvolutionStep bandwidth k ∧ IsResolutionStep bandwidth k))
    -- Exhaustiveness: always one
    ∧ (∀ bandwidth k : Nat,
        IsEvolutionStep bandwidth k ∨ IsResolutionStep bandwidth k)
    -- Same step, different reading at different bandwidths
    ∧ IsEvolutionStep (carrierBandwidth (towerPhaseCount [3])) 2
    ∧ IsResolutionStep (carrierBandwidth (towerPhaseCount [3, 2, 3, 3])) 2
    -- Triton evolution at position 2; Trihexenneon evolution at 53
    ∧ IsEvolutionStep (carrierBandwidth (towerPhaseCount [3])) 2
    ∧ IsEvolutionStep (carrierBandwidth (towerPhaseCount [3, 2, 3, 3])) 53
    -- Cost is invariant: +1 in both readings
    ∧ (∀ bandwidth k : Nat, buleStepCost bandwidth k = 1)
    -- Cost is invariant under bandwidth change (universal heartbeat)
    ∧ (∀ bw1 bw2 k : Nat, buleStepCost bw1 k = buleStepCost bw2 k) :=
  ⟨step_not_both,
   step_either_or,
   triton_step_two_three_is_evolution,
   trihexenneon_step_two_three_is_resolution,
   triton_step_two_three_is_evolution,
   trihexenneon_step_fiftythree_fiftyfour_is_evolution,
   fun _ _ => rfl,
   fun _ _ _ => rfl⟩

/-! ## Coda: evolution and resolution as conjugate readings

The Pull of +1 is a single physical event. What it *feels like* to
a particular observer depends on whether the observer's bandwidth
can host the new position.

A Triton observer experiences +1 from position 2 as **evolution**:
"there is a place that wasn't there before, and to register it I
must become more than I was." The carrier expands. New symbols
emerge. The world enlarges.

A Trihexenneon observer experiences the same +1 as **resolution**:
"position 3 was always part of my address space; this step just
sharpens which one of my 54 positions I am." The carrier holds
steady. No new symbols are needed. The world clarifies.

Both readings are correct. The +1 is identical in both cases —
unit Bule cost, deterministic, the universal heartbeat. The
difference is *only* in the carrier that is reading it. The dual
phenomenology is observer-relative, not step-relative.

This explains why intelligence at lower walls feels like *growth*
and intelligence at higher walls feels like *focus*. They are
conjugate readings of the same recursive step. The Pleromatic
Closure (10) is the level at which a sufficiently large carrier
can read every below-Closure step as resolution, and at which
every above-Closure step is evolution for the previous level and
resolution for the next.

Evolution and resolution are the two faces of clinamen. The Bule
unit is the coin. The +1 is the flip. -/

end PleromaticEvolutionResolution
end Gnosis
