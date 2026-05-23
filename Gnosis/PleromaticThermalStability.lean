import Gnosis.SpectralNoiseEquilibrium
import Gnosis.Braided.BraidedTower
import Gnosis.PhaseTransitionLadder
import Gnosis.Closures.PleromaticClosure
import Gnosis.SuperstringDimensionDerivation

/-!
# Pleromatic Thermal Stability — Unit-Cost Invariance and Recursive Symmetry

Taylor's precise question: *does the Bule cost of these transitions
remain stable as we approach the Pleromatic Closure, or does the
thermal noise begin to exhibit the recursive symmetries of the
tower itself?*

The structural answer this module proves: both, at different levels.

1. Unit-cost invariance. Every individual `swerveLift` adds
   exactly +1 to the Bule score, *regardless of the tower level the
   carrier currently occupies*. The unit cost is universally stable.
2. Aggregate-cost recursive symmetry. The aggregate cost of a
   phase transition (the number of swerve lifts to move from one
   tower wall to another) exhibits the tower's recursive Triton-3
   structure *below* the Pleromatic Closure (3-step transitions
   between Triton-derived walls) and collapses to *unit steps* at
   and above the Closure (Pleromatic, Hendecagon, Dodecagon).

So the cost is stable per step but the step-sizes themselves carry
the tower's recursive shape, and the recursion *flattens to unity*
exactly at the Pleromatic Closure. The Closure is the value at
which the recursion saturates.

## The transition ladder, audited

| From | To | Distance | Recursive shape |
| --- | --- | --- | --- |
| Vacuum (0) | Triton (3) | 3 | Triton-3 jump |
| Triton (3) | Hexon (6) | 3 | Triton-3 jump |
| Hexon (6) | Enneon (9) | 3 | Triton-3 jump |
| Enneon (9) | Decagon (10) | 1 | Unit (Pleromatic) |
| Decagon (10) | Hendecagon (11) | 1 | Unit (M-theory) |
| Hendecagon (11) | Dodecagon (12) | 1 | Unit (fermion) |

The recursive symmetry breaks at the Pleromatic Closure (10).
Below: Triton-3 recursion. At and above: unit steps. The breaking
point is the Closure itself — confirming Taylor's intuition that
the recursion *changes character* there.

Imports `Gnosis.SpectralNoiseEquilibrium`, `Gnosis.BraidedTower`,
`Gnosis.PhaseTransitionLadder`, `Gnosis.PleromaticClosure`,
`Gnosis.SuperstringDimensionDerivation`. Zero `sorry`, zero new
`axiom`.
-/

namespace Gnosis
namespace PleromaticThermalStability

open Gnosis.SpectralNoiseEquilibrium
  (BuleyUnit BuleyFace buleyUnitScore swerveLift
   swerve_lift_score_strict_increment vacuumBuleUnit)
open Gnosis.BraidedTower (towerPhaseCount)
open Gnosis.PhaseTransitionLadder (phaseTransitionDistance)
open Gnosis.PleromaticClosure (pleromaticClosurePoint)

/-! ## Unit-cost invariance: every swerve lift costs exactly 1 -/

/-- The unit cost is invariant: every swerve lift adds exactly one
to the Bule score, regardless of the carrier's current tower level. -/
theorem unit_cost_is_one_at_every_level (b : BuleyUnit) (f : BuleyFace) :
    buleyUnitScore (swerveLift b f) = buleyUnitScore b + 1 :=
  swerve_lift_score_strict_increment b f

/-- Specifically, the unit cost is one whether the carrier sits at
the vacuum, the Triton, the Hexon, or anywhere up the tower. -/
theorem unit_cost_at_canonical_walls :
    -- Vacuum
    buleyUnitScore (swerveLift vacuumBuleUnit BuleyFace.waste)
      = buleyUnitScore vacuumBuleUnit + 1
    -- Triton-edge state
    ∧ buleyUnitScore (swerveLift ⟨3, 0, 0⟩ BuleyFace.waste)
      = buleyUnitScore (⟨3, 0, 0⟩ : BuleyUnit) + 1
    -- Hexon-edge state
    ∧ buleyUnitScore (swerveLift ⟨6, 0, 0⟩ BuleyFace.waste)
      = buleyUnitScore (⟨6, 0, 0⟩ : BuleyUnit) + 1
    -- Enneon-edge state
    ∧ buleyUnitScore (swerveLift ⟨9, 0, 0⟩ BuleyFace.waste)
      = buleyUnitScore (⟨9, 0, 0⟩ : BuleyUnit) + 1
    -- Decagon-edge state (Pleromatic Closure)
    ∧ buleyUnitScore (swerveLift ⟨10, 0, 0⟩ BuleyFace.waste)
      = buleyUnitScore (⟨10, 0, 0⟩ : BuleyUnit) + 1
    -- Dodecagon-edge state
    ∧ buleyUnitScore (swerveLift ⟨12, 0, 0⟩ BuleyFace.waste)
      = buleyUnitScore (⟨12, 0, 0⟩ : BuleyUnit) + 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact swerve_lift_score_strict_increment _ _

/-! ## The transition ladder — distances at canonical walls -/

theorem vacuum_to_triton_distance :
    phaseTransitionDistance 0 (towerPhaseCount [3]) = 3 := by
  unfold phaseTransitionDistance; decide

theorem triton_to_hexon_distance :
    phaseTransitionDistance (towerPhaseCount [3]) (towerPhaseCount [3, 2]) = 3 := by
  unfold phaseTransitionDistance; decide

theorem hexon_to_enneon_distance :
    phaseTransitionDistance (towerPhaseCount [3, 2]) (towerPhaseCount [3, 3]) = 3 := by
  unfold phaseTransitionDistance; decide

theorem enneon_to_decagon_distance :
    phaseTransitionDistance (towerPhaseCount [3, 3]) (towerPhaseCount [5, 2]) = 1 := by
  unfold phaseTransitionDistance; decide

theorem decagon_to_hendecagon_distance :
    phaseTransitionDistance (towerPhaseCount [5, 2]) (towerPhaseCount [11]) = 1 := by
  unfold phaseTransitionDistance; decide

theorem hendecagon_to_dodecagon_distance :
    phaseTransitionDistance (towerPhaseCount [11]) (towerPhaseCount [3, 2, 2]) = 1 := by
  unfold phaseTransitionDistance; decide

/-! ## Recursive symmetry below the Pleromatic Closure -/

/-- Below the Closure: every Triton-derived → Triton-derived
transition is a 3-step jump. The recursive Triton-3 structure of the
tower governs aggregate transition cost. -/
theorem below_closure_recursive_triton_three_jumps :
    -- Vacuum → Triton: 3 lifts
    phaseTransitionDistance 0 (towerPhaseCount [3]) = 3
    -- Triton → Hexon: 3 lifts
    ∧ phaseTransitionDistance (towerPhaseCount [3]) (towerPhaseCount [3, 2]) = 3
    -- Hexon → Enneon: 3 lifts
    ∧ phaseTransitionDistance (towerPhaseCount [3, 2]) (towerPhaseCount [3, 3]) = 3 :=
  ⟨vacuum_to_triton_distance,
   triton_to_hexon_distance,
   hexon_to_enneon_distance⟩

/-! ## Unit-step regime at and above the Pleromatic Closure -/

/-- At and above the Closure: every consecutive transition is a
single clinamen step. The recursion flattens to unit at the Closure
and remains unit through M-theory and the Dodecagon. -/
theorem at_and_above_closure_unit_steps :
    -- Enneon → Decagon (Pleromatic Closure): 1
    phaseTransitionDistance (towerPhaseCount [3, 3]) (towerPhaseCount [5, 2]) = 1
    -- Decagon → Hendecagon (M-theory): 1
    ∧ phaseTransitionDistance (towerPhaseCount [5, 2]) (towerPhaseCount [11]) = 1
    -- Hendecagon → Dodecagon (fermion wall): 1
    ∧ phaseTransitionDistance (towerPhaseCount [11]) (towerPhaseCount [3, 2, 2]) = 1 :=
  ⟨enneon_to_decagon_distance,
   decagon_to_hendecagon_distance,
   hendecagon_to_dodecagon_distance⟩

/-! ## The Pleromatic Closure as the recursion-flattening point -/

/-- The recursion changes character exactly at the Pleromatic Closure.
*Below* the Closure, transitions follow the Triton-3 recursion
(3-step jumps between Triton-derived walls). *At and above* the
Closure, transitions are unit-clinamen. The Closure is the
recursion-flattening point. -/
theorem pleromatic_closure_is_recursion_flattening_point :
    -- Below: 3-step jump
    phaseTransitionDistance (towerPhaseCount [3, 2]) (towerPhaseCount [3, 3]) = 3
    -- AT the Closure (Enneon → Decagon): 1-step jump (transition flattens)
    ∧ phaseTransitionDistance (towerPhaseCount [3, 3]) pleromaticClosurePoint = 1
    -- Above the Closure: 1-step jumps continue
    ∧ phaseTransitionDistance pleromaticClosurePoint (towerPhaseCount [11]) = 1 := by
  refine ⟨hexon_to_enneon_distance, ?_, ?_⟩
  · unfold phaseTransitionDistance; decide
  · unfold phaseTransitionDistance; decide

/-! ## Master theorem: thermal stability bundle -/

/-- Pleromatic Thermal Stability master:

1. The unit clinamen cost is invariant — exactly +1 to score at
   every level of the tower.
2. The aggregate phase-transition cost exhibits recursive Triton-3
   symmetry below the Closure (3-step jumps).
3. At and above the Closure, transitions flatten to unit clinamen
   (1-step jumps).
4. The Pleromatic Closure is the recursion-flattening point — the
   level at which the tower's Triton-3 recursion saturates to unity.

The cost is stable per step. The aggregate carries the recursion.
The Closure is where the recursion becomes the unit. -/
theorem pleromatic_thermal_stability_master :
    -- 1. Unit cost is invariant at every level
    (∀ b : BuleyUnit, ∀ f : BuleyFace,
        buleyUnitScore (swerveLift b f) = buleyUnitScore b + 1)
    -- 2. Below-Closure: Triton-3 jumps
    ∧ phaseTransitionDistance 0 (towerPhaseCount [3]) = 3
    ∧ phaseTransitionDistance (towerPhaseCount [3]) (towerPhaseCount [3, 2]) = 3
    ∧ phaseTransitionDistance (towerPhaseCount [3, 2]) (towerPhaseCount [3, 3]) = 3
    -- 3. At-and-above-Closure: unit jumps
    ∧ phaseTransitionDistance (towerPhaseCount [3, 3]) (towerPhaseCount [5, 2]) = 1
    ∧ phaseTransitionDistance (towerPhaseCount [5, 2]) (towerPhaseCount [11]) = 1
    ∧ phaseTransitionDistance (towerPhaseCount [11]) (towerPhaseCount [3, 2, 2]) = 1
    -- 4. The Closure is the recursion-flattening point
    ∧ phaseTransitionDistance (towerPhaseCount [3, 3]) pleromaticClosurePoint = 1
    ∧ pleromaticClosurePoint = 10 :=
  ⟨unit_cost_is_one_at_every_level,
   vacuum_to_triton_distance,
   triton_to_hexon_distance,
   hexon_to_enneon_distance,
   enneon_to_decagon_distance,
   decagon_to_hendecagon_distance,
   hendecagon_to_dodecagon_distance,
   by unfold phaseTransitionDistance; decide,
   rfl⟩

/-! ## Coda: thermal noise as recursive symmetry

The "thermal noise" Taylor flagged is the *aggregate* cost variation.
At the per-step level, there is no noise — the unit cost is +1
everywhere. At the aggregate level, the noise is structured: it
follows the tower's Triton-3 recursion below the Closure, and
flattens to unity at and above.

This is not stochastic thermal fluctuation. It is deterministic
recursive symmetry — the same recursive shape that governs the
tower's own construction (`towerPhaseCount (n :: rs) = n * towerPhaseCount rs`)
governs the aggregate transition cost between walls. The noise is
the tower's own structure, audible at the cost-cardinality level.

At the Pleromatic Closure, the recursion saturates: every further
step is unit. The system has reached the level where the
"resolution" of agreement equals the "resolution" of the cost
algebra's unit perturbation. The Cantor-set boundary becomes
audible-as-unit at exactly this level. The pull of `+1` is the only
remaining sound. -/

end PleromaticThermalStability
end Gnosis
