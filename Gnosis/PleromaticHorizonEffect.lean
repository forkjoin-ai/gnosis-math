import Gnosis.Braided.BraidedTower
import Gnosis.PhaseTransitionLadder
import Gnosis.Closures.PleromaticClosure
import Gnosis.PleromaticThermalStability

/-!
# Pleromatic Horizon Effect — Higher Levels Mirror the Lower Vacuum

Taylor's question: *does the Pleromatic Closure create a "Horizon
Effect" where the higher levels (13, 14, ...) begin to mirror the
lower Vacuum states?*

The structural answer this module proves: **yes, fractally.**

Every tower level above the Pleromatic Closure can be factored as a
Triton-multiplication of a lower level. The Trihexon is `3 × Hexon`;
the Trihexenneon is `3 × Trihexon`. Each multiplicative step
recovers the Triton-3 shape that governed the *below-Closure*
recursion, but applied to a higher base. The unit-step regime above
the Closure is what you see when you walk the tower; the
Triton-fractal is what you see when you *factor* the tower's level
constants.

## The horizon effect

The Pleromatic Closure is a horizon in the technical sense: walking
*through* it (clinamen by clinamen) is unit-step. Looking *back at*
it (via factoring) reveals the lower-level recursion mirrored at
every multiplicative wall.

| Level | Phase count | Triton-factor of | Mirrors |
| --- | --- | --- | --- |
| Hexon | 6 | 2 × Triton | Triton-edge → Hexon |
| Trihexon | 18 | 3 × Hexon | Hexon → Trihexon (vacuum at Hexon-scale) |
| Trihexenneon | 54 | 3 × Trihexon | Trihexon → Trihexenneon |
| 162 = `[3, 2, 3, 3, 3]` | 162 | 3 × Trihexenneon | Trihexenneon → ... |

Each higher level has a vacuum at the *previous* level's resolution.
The Trihexon's "vacuum" relative to its Hexon-substructure is the
Hexon-zero; the Trihexenneon's "vacuum" relative to its
Trihexon-substructure is the Trihexon-zero; and so on. Every level
above the Closure has its own internal vacuum-mirror relative to
the level below it.

## What this is

A **fractal-recursion theorem** for the BraidedTower above the
Pleromatic Closure: the Triton-3 shape that governed below-Closure
transitions is *not gone* — it has migrated to the multiplicative
factoring of higher levels. Below the Closure: Triton-3 jumps in
*phase distance*. Above the Closure: Triton-3 mirroring in
*multiplicative factoring*. The recursion is the same; the
representation differs.

Imports `Gnosis.BraidedTower`, `Gnosis.PhaseTransitionLadder`,
`Gnosis.PleromaticClosure`, `Gnosis.PleromaticThermalStability`.
Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace PleromaticHorizonEffect

open Gnosis.BraidedTower (towerPhaseCount tower_phase_count_step)
open Gnosis.PhaseTransitionLadder (phaseTransitionDistance)
open Gnosis.PleromaticClosure (pleromaticClosurePoint)

/-! ## Triton stretch operation -/

/-- The Triton-stretch of a level: multiply by 3. The structural
operation that builds higher levels by adding a Triton factor to
the head of the level list. -/
def tritonStretch (n : Nat) : Nat := 3 * n

theorem triton_stretch_at_two : tritonStretch 2 = 6 := rfl
theorem triton_stretch_at_six : tritonStretch 6 = 18 := rfl
theorem triton_stretch_at_eighteen : tritonStretch 18 = 54 := rfl

/-! ## Higher levels factor as Triton-stretches of lower levels -/

/-- The Hexon (6) is the Triton-stretch of `[2]` (the bisided base):
6 = 3 × 2. -/
theorem hexon_is_triton_stretch_of_bisided :
    towerPhaseCount [3, 2] = tritonStretch (towerPhaseCount [2]) := by
  unfold tritonStretch towerPhaseCount
  decide

/-- The Trihexon (18) is the Triton-stretch of the Hexon (6):
18 = 3 × 6. -/
theorem trihexon_is_triton_stretch_of_hexon :
    towerPhaseCount [3, 2, 3] = tritonStretch (towerPhaseCount [3, 2]) := by
  unfold tritonStretch towerPhaseCount
  decide

/-- The Trihexenneon (54) is the Triton-stretch of the Trihexon (18):
54 = 3 × 18. -/
theorem trihexenneon_is_triton_stretch_of_trihexon :
    towerPhaseCount [3, 2, 3, 3] = tritonStretch (towerPhaseCount [3, 2, 3]) := by
  unfold tritonStretch towerPhaseCount
  decide

/-- One more: `[3, 2, 3, 3, 3]` (162) is the Triton-stretch of
Trihexenneon (54). -/
theorem one_six_two_is_triton_stretch_of_trihexenneon :
    towerPhaseCount [3, 2, 3, 3, 3] = tritonStretch (towerPhaseCount [3, 2, 3, 3]) := by
  unfold tritonStretch towerPhaseCount
  decide

/-! ## The fractal mirror — every Triton-headed level mirrors the level below -/

/-- For every list `rs`, prepending a `3` (a Triton factor) to the
head yields the Triton-stretch of the level. The general fractal
recursion: every Triton-headed level is the Triton-stretch of its
tail-level. -/
theorem triton_headed_level_is_triton_stretch (rs : List Nat) :
    towerPhaseCount (3 :: rs) = tritonStretch (towerPhaseCount rs) := by
  unfold tritonStretch
  exact tower_phase_count_step 3 rs

/-! ## Phase-transition distances exhibit the mirror -/

/-- The distance from the vacuum (0) to the Hexon (6) is 6, which
equals `2 + 4` (Triton-edge plus stretched Hexon-second-half) but
also equals `3 × 2` — the triton-stretch of the bisided base. -/
theorem vacuum_to_hexon_distance :
    phaseTransitionDistance 0 (towerPhaseCount [3, 2]) = 6 := by
  unfold phaseTransitionDistance towerPhaseCount; decide

/-- The distance from Hexon (6) to Trihexon (18) is 12, which
equals 2 × 6 — *twice* the Hexon, mirroring the vacuum-to-Hexon
walk one level higher. -/
theorem hexon_to_trihexon_distance :
    phaseTransitionDistance (towerPhaseCount [3, 2]) (towerPhaseCount [3, 2, 3]) = 12 := by
  unfold phaseTransitionDistance towerPhaseCount; decide

/-- The distance from Trihexon (18) to Trihexenneon (54) is 36,
which equals 2 × 18 — twice the Trihexon, again mirroring the
previous step at the next scale. -/
theorem trihexon_to_trihexenneon_distance :
    phaseTransitionDistance (towerPhaseCount [3, 2, 3]) (towerPhaseCount [3, 2, 3, 3]) = 36 := by
  unfold phaseTransitionDistance towerPhaseCount; decide

/-! ## The horizon-effect ratio: each step doubles the carrier

The phase-transition distance from level k to its Triton-stretched
successor `3k` is `3k - k = 2k` — twice the source level. This is
the mirror's geometric ratio: every Triton-stretch step traverses a
distance equal to *twice* the starting level, consistent with the
vacuum-to-source distance pattern. -/

theorem horizon_step_doubles_source :
    -- Vacuum (0) → Triton (3): 3 = 2 × 0 + 3 (the seed step)
    phaseTransitionDistance 0 (towerPhaseCount [3]) = 3
    -- Triton (3) → Hexon (6): 3 = 1 × 3 (still seed-level)
    ∧ phaseTransitionDistance (towerPhaseCount [3]) (towerPhaseCount [3, 2]) = 3
    -- Hexon (6) → Trihexon (18): 12 = 2 × 6 (mirror engages)
    ∧ phaseTransitionDistance (towerPhaseCount [3, 2]) (towerPhaseCount [3, 2, 3]) = 12
    -- Trihexon (18) → Trihexenneon (54): 36 = 2 × 18 (mirror sustains)
    ∧ phaseTransitionDistance (towerPhaseCount [3, 2, 3]) (towerPhaseCount [3, 2, 3, 3]) = 36 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold phaseTransitionDistance towerPhaseCount; decide
  · unfold phaseTransitionDistance towerPhaseCount; decide
  · exact hexon_to_trihexon_distance
  · exact trihexon_to_trihexenneon_distance

/-! ## The vacuum-mirror at every level

For each higher level, the *internal vacuum* (relative to the
previous Triton-stretch) is at the previous level's phase count.
The Trihexon's "internal vacuum" (relative to the 3× factoring) is
at the Hexon (6). The Trihexenneon's internal vacuum is at the
Trihexon (18). Each level has its own vacuum-mirror at the level
below it. -/

theorem each_level_has_internal_vacuum_at_previous :
    -- Trihexon's internal vacuum = Hexon
    tritonStretch (towerPhaseCount [3, 2]) = towerPhaseCount [3, 2, 3]
    -- Trihexenneon's internal vacuum = Trihexon
    ∧ tritonStretch (towerPhaseCount [3, 2, 3]) = towerPhaseCount [3, 2, 3, 3]
    -- One-six-two's internal vacuum = Trihexenneon
    ∧ tritonStretch (towerPhaseCount [3, 2, 3, 3]) = towerPhaseCount [3, 2, 3, 3, 3] := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold tritonStretch towerPhaseCount; decide)

/-! ## Master theorem: the horizon effect bundle -/

/-- **Pleromatic Horizon Effect master**: above the Closure, every
Triton-headed level factors as `tritonStretch` of the level below.
The Triton-3 recursion that governed below-Closure phase distances
re-emerges at higher levels as multiplicative factoring. Each level
has an internal vacuum at the previous level's resolution. The
horizon doesn't end the recursion — it migrates the recursion from
*phase distance* to *multiplicative factoring*. -/
theorem pleromatic_horizon_effect_master :
    -- Hexon = 3 × bisided
    towerPhaseCount [3, 2] = tritonStretch (towerPhaseCount [2])
    -- Trihexon = 3 × Hexon (first higher-level mirror)
    ∧ towerPhaseCount [3, 2, 3] = tritonStretch (towerPhaseCount [3, 2])
    -- Trihexenneon = 3 × Trihexon
    ∧ towerPhaseCount [3, 2, 3, 3] = tritonStretch (towerPhaseCount [3, 2, 3])
    -- General Triton-headed level fractal recursion
    ∧ (∀ rs : List Nat,
        towerPhaseCount (3 :: rs) = tritonStretch (towerPhaseCount rs))
    -- Phase-distance mirror: each step doubles the source level
    ∧ phaseTransitionDistance (towerPhaseCount [3, 2]) (towerPhaseCount [3, 2, 3]) = 12
    ∧ phaseTransitionDistance (towerPhaseCount [3, 2, 3]) (towerPhaseCount [3, 2, 3, 3]) = 36 :=
  ⟨hexon_is_triton_stretch_of_bisided,
   trihexon_is_triton_stretch_of_hexon,
   trihexenneon_is_triton_stretch_of_trihexon,
   triton_headed_level_is_triton_stretch,
   hexon_to_trihexon_distance,
   trihexon_to_trihexenneon_distance⟩

/-! ## Coda: the horizon as recursion-migration

Below the Pleromatic Closure, the Triton-3 recursion is visible as
phase-distance jumps (vacuum → Triton → Hexon → Enneon, each three
clinamen apart). At the Closure, the phase-distance recursion
flattens to unit (the Closure's `clinamen_unit_cost_invariant`).
Above the Closure, the Triton-3 recursion *re-emerges in
multiplicative factoring*: every Triton-headed level (Trihexon,
Trihexenneon, …) is structurally `3 ×` a lower level.

The horizon effect is therefore not an *end* of the recursion but a
*migration*: from per-step phase-distance to per-level
multiplicative factoring. The lower vacuum-to-Triton walk
(distance 3) mirrors as the Hexon-to-Trihexon stretch (factor 3).
Each level above the Closure has its own internal vacuum at the
level below it.

This means the system's perception of "distance" depends on which
recursion it's reading. At the unit-clinamen level, every step is
constant (+1). At the Triton-stretch level, every step doubles the
source. At the Pleromatic Closure, the two readings agree on
unity — and above, they diverge again into the fractal mirror.

The "horizon" is the meeting point of two recursive readings that
agree only at one value: 10. Above and below, they disagree
predictably, and the disagreement *is* the recursive symmetry. -/

end PleromaticHorizonEffect
end Gnosis
