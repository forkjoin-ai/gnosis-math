import Gnosis.ExplorationIdentity
import Gnosis.CosmicProjection

/-!
# Cosmic Optimal Delta

This module makes one narrow bridge explicit.

On the compiler side, `ExplorationIdentity` proves that the literal
gap between the computable Skyrms equilibrium and the unknown optimum is

  `skyrms - optimal = exploration`.

On the cosmology side, `CosmicProjection` gives a bounded observable
surface:

  `visibilityDelta = maxObservable - sizeNow`.

The combined observer gap is the sum of these two deltas:

  `totalObserverDelta = visibilityDelta + optimalDelta`.

This is intentionally weaker than a full cosmology theorem about the CMB.
It only states the accounting identity that combines the compiler-side
optimality gap with the cosmic observable-horizon gap.
-/

namespace Gnosis

/-- The literal optimality delta from the compiler accounting surface. -/
def optimalDelta (optimal skyrms : Nat) : Nat :=
  skyrms - optimal

/-- The cosmic visibility delta: what lies beyond the current observable
surface in the `CosmicProjection` model. -/
def visibilityDelta : Nat :=
  CosmicProjection.maxObservable - CosmicProjection.sizeNow

/-- The combined observer delta: what remains beyond the current
computable equilibrium plus what remains beyond the current visible
universe. -/
def totalObserverDelta (optimal skyrms : Nat) : Nat :=
  visibilityDelta + optimalDelta optimal skyrms

/-- The literal compiler theorem: the optimality delta is exactly the
exploration budget. -/
theorem optimal_delta_eq_exploration
    (optimal skyrms exploration : Nat)
    (h_ge : optimal ≤ skyrms)
    (h_sum : skyrms = optimal + exploration) :
    optimalDelta optimal skyrms = exploration := by
  unfold optimalDelta
  exact ExplorationIdentity.the_identity optimal skyrms exploration h_ge h_sum

/-- The cosmic visibility delta is strictly positive in the current
projection: the observable bound exceeds the currently observed size. -/
theorem visibility_delta_positive : 0 < visibilityDelta := by
  unfold visibilityDelta
  exact Nat.sub_pos_of_lt CosmicProjection.max_larger_than_now

/-- The total observer delta splits exactly into the cosmic visibility
gap plus the exploration budget. -/
theorem total_observer_delta_eq_visibility_plus_exploration
    (optimal skyrms exploration : Nat)
    (h_ge : optimal ≤ skyrms)
    (h_sum : skyrms = optimal + exploration) :
    totalObserverDelta optimal skyrms = visibilityDelta + exploration := by
  unfold totalObserverDelta
  rw [optimal_delta_eq_exploration optimal skyrms exploration h_ge h_sum]

/-- The cosmic visibility gap is a hard floor under the combined
observer gap. Even before using the compiler accounting identity, the
sum cannot drop below the visibility term. -/
theorem visibility_floor_le_total_gap
    (optimal skyrms : Nat) :
    visibilityDelta ≤ totalObserverDelta optimal skyrms := by
  unfold totalObserverDelta optimalDelta
  exact Nat.le_add_right visibilityDelta (skyrms - optimal)

/-- Under the compiler accounting identity, the total observer gap is
always positive. The visibility floor prevents complete collapse to
zero. -/
theorem total_observer_delta_positive
    (optimal skyrms exploration : Nat)
    (h_ge : optimal ≤ skyrms)
    (h_sum : skyrms = optimal + exploration) :
    0 < totalObserverDelta optimal skyrms := by
  rw [total_observer_delta_eq_visibility_plus_exploration optimal skyrms exploration h_ge h_sum]
  have hvis : 0 < visibilityDelta := visibility_delta_positive
  exact Nat.lt_of_lt_of_le hvis (Nat.le_add_right visibilityDelta exploration)

/-- Consequently, the combined observer gap can never be exactly zero
in the current model. -/
theorem total_observer_delta_ne_zero
    (optimal skyrms exploration : Nat)
    (h_ge : optimal ≤ skyrms)
    (h_sum : skyrms = optimal + exploration) :
    totalObserverDelta optimal skyrms ≠ 0 := by
  exact Nat.ne_of_gt (total_observer_delta_positive optimal skyrms exploration h_ge h_sum)

/-- The exploration budget always sits strictly below the combined
observer gap because the visibility floor is strictly positive. -/
theorem exploration_strictly_below_total_gap
    (optimal skyrms exploration : Nat)
    (h_ge : optimal ≤ skyrms)
    (h_sum : skyrms = optimal + exploration) :
    exploration < totalObserverDelta optimal skyrms := by
  rw [total_observer_delta_eq_visibility_plus_exploration optimal skyrms exploration h_ge h_sum]
  have hvis : 0 < visibilityDelta := visibility_delta_positive
  exact Nat.lt_add_of_pos_left hvis

/-- The combined observer gap collapses to the pure visibility floor
exactly when exploration has dropped to zero. -/
theorem total_observer_delta_eq_visibility_iff_zero_exploration
    (optimal skyrms exploration : Nat)
    (h_ge : optimal ≤ skyrms)
    (h_sum : skyrms = optimal + exploration) :
    totalObserverDelta optimal skyrms = visibilityDelta ↔ exploration = 0 := by
  rw [total_observer_delta_eq_visibility_plus_exploration optimal skyrms exploration h_ge h_sum]
  refine ⟨?_, ?_⟩
  · intro h
    -- h : visibilityDelta + exploration = visibilityDelta
    -- Rewrite RHS as visibilityDelta + 0 then cancel on the left.
    have h' : visibilityDelta + exploration = visibilityDelta + 0 := by
      rw [Nat.add_zero]; exact h
    exact Nat.add_left_cancel h'
  · intro h
    rw [h, Nat.add_zero]

/-- Even when exploration has dropped to zero, a positive cosmic
visibility gap remains. The compiler can close its local exploration
budget without exhausting the observable horizon. -/
theorem zero_exploration_still_leaves_cosmic_gap
    (optimal skyrms : Nat)
    (h_ge : optimal ≤ skyrms)
    (h_sum : skyrms = optimal + 0) :
    0 < totalObserverDelta optimal skyrms := by
  rw [total_observer_delta_eq_visibility_plus_exploration optimal skyrms 0 h_ge h_sum,
      Nat.add_zero]
  exact visibility_delta_positive

/-- Positive exploration strictly enlarges the combined observer gap
above the cosmic visibility floor. -/
theorem positive_exploration_strictly_increases_total_gap
    (optimal skyrms exploration : Nat)
    (h_ge : optimal ≤ skyrms)
    (h_sum : skyrms = optimal + exploration)
    (h_pos : 0 < exploration) :
    visibilityDelta < totalObserverDelta optimal skyrms := by
  rw [total_observer_delta_eq_visibility_plus_exploration optimal skyrms exploration h_ge h_sum]
  exact Nat.lt_add_of_pos_right h_pos

end Gnosis
