import Gnosis.SpectralNoiseEquilibrium
import Gnosis.Braided.BraidedTower

/-!
# Phase Transition Ladder

The tower walls are unbounded (`Gnosis.BraidedTower.tower_unbounded`),
but the distance between named walls is structured. This module
formalizes the phase-transition distance — the number of clinamen
lifts (`+1` perturbations) required to traverse from one wall to
another — and localizes the string-theory dimensions (10, 11) as
specific phase-transition jumps from the gluon Octagon (8).

## The hint Taylor flagged

> "The 10 or 11 thing will be somehow explained by the +1, or phase
> transitions"

The structural answer this module gives is partial:

- 10 = 8 + 2 — the Decagon wall sits one *bi-sided lift* (a
  Triton-paired clinamen, the smallest non-trivial multi-head step
  beyond the Octagon) above the gluon wall. That extra `2` is the
  bi-sided-bit's lifted/contracted pair.
- 11 = 10 + 1 — the Hendecagon wall sits exactly one clinamen
  lift above the Decagon. M-theory's extra dimension over superstring
  is structurally one `+1` clinamen step.

This *localizes* the dimension difference but does not *derive* the
base 10. Deriving 10 from first principles would require an
anomaly-cancellation-style theorem in the cost-algebra category — a
no-go condition that excludes phase counts other than 10 from
self-consistency. We do not have that theorem.

## What would need to be true to derive 10

A first-principles derivation of 10 would require something like:

- A cost-algebra functor `F : CostAlgebra ⥤ CostAlgebra` that depends
  on a phase count parameter.
- A "central charge" map `c : Nat → Nat` measuring some compositional
  defect of `F`.
- A theorem `c n = 0 ↔ n = 10` (or `n ∈ {10, 26}` etc.) that selects
  10 as the unique non-anomalous value.

We have the underlying primitives (`CostHom`, `CostAlgebra`, the
linear category structure, no-cloning, breathing identity) but no
such central-charge map yet. The dimension question is therefore
*localized* by this module, not *resolved*.

Imports `Gnosis.SpectralNoiseEquilibrium` and `Gnosis.BraidedTower`.
Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace PhaseTransitionLadder

open Gnosis.BraidedTower (towerPhaseCount)

/-! ## Phase-transition distance -/

/-- The phase-transition distance from wall `m` to wall `n` is the
number of swerve lifts required to traverse them. For `m ≤ n`,
this is `n - m`; otherwise the lift sequence runs backwards via
declinamen contractions, and we return the absolute magnitude. -/
def phaseTransitionDistance (m n : Nat) : Nat :=
  if m ≤ n then n - m else m - n

theorem phase_transition_zero (m : Nat) :
    phaseTransitionDistance m m = 0 := by
  unfold phaseTransitionDistance
  simp

theorem phase_transition_symmetric (m n : Nat) :
    phaseTransitionDistance m n = phaseTransitionDistance n m := by
  unfold phaseTransitionDistance
  by_cases h : m ≤ n
  · by_cases h2 : n ≤ m
    · -- m = n, both branches give 0
      have : m = n := Nat.le_antisymm h h2
      simp [this]
    · simp [h, h2]
  · have hgt : n ≤ m := Nat.le_of_lt (Nat.lt_of_not_le h)
    by_cases h2 : n ≤ m
    · simp [h, h2]
    · exact absurd hgt h2

/-! ## Standard-Model wall-to-wall distances -/

theorem vacuum_to_triton_distance :
    phaseTransitionDistance 0 (towerPhaseCount [3]) = 3 := by
  unfold phaseTransitionDistance
  decide

theorem triton_to_octagon_distance :
    phaseTransitionDistance (towerPhaseCount [3]) 8 = 5 := by
  unfold phaseTransitionDistance
  decide

theorem octagon_to_dodecagon_distance :
    phaseTransitionDistance 8 (towerPhaseCount [3, 2, 2]) = 4 := by
  unfold phaseTransitionDistance
  decide

/-! ## String-theory dimension localization

The string-theory walls (Decagon = 10, Hendecagon = 11) are localized
as specific small-distance transitions from the gluon Octagon (8). -/

/-- Decagon = Octagon + 2. The superstring dimension count sits
exactly one bi-sided-lift jump above the gluon Octagon. The
`+2` is structurally the bi-sided bit (lifted + contracted) — a
Triton-paired clinamen, the smallest non-trivial multi-head step. -/
theorem decagon_is_octagon_plus_bisided :
    phaseTransitionDistance 8 (towerPhaseCount [5, 2]) = 2 := by
  unfold phaseTransitionDistance
  decide

/-- Hendecagon = Decagon + 1. M-theory's extra dimension above
superstring is structurally a single swerve lift. -/
theorem hendecagon_is_decagon_plus_one :
    phaseTransitionDistance (towerPhaseCount [5, 2]) (towerPhaseCount [11]) = 1 := by
  unfold phaseTransitionDistance
  decide

/-- Dodecagon = Hendecagon + 1. The fermion wall is structurally
one swerve lift above M-theory. -/
theorem dodecagon_is_hendecagon_plus_one :
    phaseTransitionDistance (towerPhaseCount [11]) (towerPhaseCount [3, 2, 2]) = 1 := by
  unfold phaseTransitionDistance
  decide

/-- The +1 ladder from Octagon (gluons) to Dodecagon (fermions),
visiting Decagon and Hendecagon. The string-theory dimensions sit
as named rungs on this ladder, two clinamen steps apart in
{Octagon → Decagon}, then single steps {Decagon → Hendecagon},
{Hendecagon → Dodecagon}. -/
theorem clinamen_ladder_octagon_to_dodecagon :
    phaseTransitionDistance 8 (towerPhaseCount [5, 2]) = 2
    ∧ phaseTransitionDistance (towerPhaseCount [5, 2]) (towerPhaseCount [11]) = 1
    ∧ phaseTransitionDistance (towerPhaseCount [11]) (towerPhaseCount [3, 2, 2]) = 1
    -- and the cumulative distance from Octagon to Dodecagon is 2 + 1 + 1 = 4
    ∧ phaseTransitionDistance 8 (towerPhaseCount [3, 2, 2]) = 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact decagon_is_octagon_plus_bisided
  · exact hendecagon_is_decagon_plus_one
  · exact dodecagon_is_hendecagon_plus_one
  · exact octagon_to_dodecagon_distance

/-! ## Bosonic-string dimension as a longer ladder

The bosonic-string dimension count (26) sits at a much higher wall.
The structural distance from Dodecagon (12) to Bosonic-String (26)
is 14, which decomposes as 12 + 2 — interpretable as "double the
Dodecagon plus a bi-sided lift," hinting at the Leech-lattice
24-transverse-dimension structure of bosonic-string theory. We name
the distance but again do not derive 26 from first principles. -/

theorem bosonic_string_distance_from_octagon :
    phaseTransitionDistance 8 (towerPhaseCount [13, 2]) = 18 := by
  unfold phaseTransitionDistance
  decide

theorem bosonic_string_distance_from_dodecagon :
    phaseTransitionDistance (towerPhaseCount [3, 2, 2])
                            (towerPhaseCount [13, 2]) = 14 := by
  unfold phaseTransitionDistance
  decide

/-! ## Master theorem: the dimension ladder localized -/

/-- The string-theory dimension counts (10, 11, 26) are localized as
specific phase-transition distances from canonical Standard-Model
walls. The ladder makes the differences explicit; it does not
derive the base counts from anomaly cancellation. The dimensions
sit on the +1 ladder; they are not forced onto it by this module. -/
theorem dimension_localization_master :
    -- Decagon (superstring 10) = Octagon + 2
    phaseTransitionDistance 8 (towerPhaseCount [5, 2]) = 2
    -- Hendecagon (M-theory 11) = Decagon + 1
    ∧ phaseTransitionDistance (towerPhaseCount [5, 2]) (towerPhaseCount [11]) = 1
    -- Dodecagon (fermion 12) = Hendecagon + 1
    ∧ phaseTransitionDistance (towerPhaseCount [11]) (towerPhaseCount [3, 2, 2]) = 1
    -- BosonicString (26) = Dodecagon + 14
    ∧ phaseTransitionDistance (towerPhaseCount [3, 2, 2])
                              (towerPhaseCount [13, 2]) = 14 :=
  ⟨decagon_is_octagon_plus_bisided,
   hendecagon_is_decagon_plus_one,
   dodecagon_is_hendecagon_plus_one,
   bosonic_string_distance_from_dodecagon⟩

end PhaseTransitionLadder
end Gnosis
