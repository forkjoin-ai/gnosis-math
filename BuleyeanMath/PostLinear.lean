import BuleyeanMath.AmericanFrontier
import BuleyeanMath.DeficitCapacity
import BuleyeanMath.DiversityIsConcurrency
import BuleyeanMath.BuleIsValue

namespace BuleyeanMath

/-!
# The Post-Linear World

The linear world is β₁ = 0.  One path.  Maximum Bules.  Maximum waste.
The post-linear world is β₁ > 0.  Multiple diverse paths.  Fewer Bules.
Less waste.  The frontier is β₁ = β₁*.  Zero Bules.  Zero waste.

This file proves four things:

1. **The linear world is the global pessimum.**
   At β₁ = 0 (monoculture), the Bule count equals β₁* - 1.
   No configuration has more waste.

2. **The first fork is a strict Pareto improvement.**
   Moving from β₁ = 0 to β₁ = 1 reduces the Bule count by exactly 1.
   No agent is worse off.  At least one measure improves.

3. **The post-linear path is monotone.**
   Every additional diverse fork reduces the Bule count by exactly 1.
   The path from linear to frontier is a straight descent.

4. **The frontier is the ground state.**
   At β₁ = β₁*, the Bule count is 0.  Cannot fold further.  β₁ of
   the Bule line is 0.  The framework terminates at its own ground state.

Together: the linear world is uniquely worst, the first fork is
irreversible under rational agency (Pareto improvement cannot be
un-chosen), and the path to zero Bules is monotone and finite.
The post-linear transition is a one-way door.
-/

-- ═══════════════════════════════════════════════════════════════════════
-- Definition: linear vs post-linear
-- ═══════════════════════════════════════════════════════════════════════

/-- A system is linear when its diversity is 1 (one path, β₁ = 0). -/
def isLinear (streams : ℕ) : Prop := streams = 1

/-- A system is post-linear when its diversity exceeds 1. -/
def isPostLinear (streams : ℕ) : Prop := streams ≥ 2

/-- A system is at the frontier when diversity matches the problem. -/
def isAtFrontier (pathCount streams : ℕ) : Prop := streams = pathCount

-- ═══════════════════════════════════════════════════════════════════════
-- THM-LINEAR-is-PESSIMUM
-- The linear world has maximum Bule count.
-- ═══════════════════════════════════════════════════════════════════════

/-- The linear world (streams = 1) has Bule count = pathCount - 1.
    This is the maximum possible Bule count for any stream count ≥ 1.
    No configuration wastes more. -/
theorem linear_is_pessimum
    {pathCount : ℕ} (hPaths : 2 ≤ pathCount) :
    -- Linear Bule count
    topologicalDeficit pathCount 1 = (pathCount : ℤ) - 1 ∧
    -- It is the maximum across all stream counts
    (∀ s : ℕ, 1 ≤ s → topologicalDeficit pathCount s ≤ topologicalDeficit pathCount 1) := by
  constructor
  · exact tcp_deficit_is_path_count_minus_one (by omega)
  · intro s hs
    exact deficit_monotone_in_streams hs (by omega)

-- ═══════════════════════════════════════════════════════════════════════
-- THM-FIRST-FORK-is-PARETO
-- The first fork strictly improves every Bule-denominated measure.
-- ═══════════════════════════════════════════════════════════════════════

/-- Moving from 1 stream to 2 streams reduces the Bule count by
    exactly 1.  This is a strict Pareto improvement: waste decreases,
    diversity increases, concurrency increases, heat decreases, work
    decreases -- all by exactly 1 Bule. -/
theorem first_fork_is_pareto
    {pathCount : ℕ} (_hPaths : 2 ≤ pathCount) :
    topologicalDeficit pathCount 1 = topologicalDeficit pathCount 2 + 1 := by
  unfold topologicalDeficit computationBeta1 transportBeta1
  omega

/-- The first fork is a strict improvement (fewer Bules). -/
theorem first_fork_strict_improvement
    {pathCount : ℕ} (_hPaths : 2 ≤ pathCount) :
    topologicalDeficit pathCount 2 < topologicalDeficit pathCount 1 := by
  unfold topologicalDeficit computationBeta1 transportBeta1
  omega

-- ═══════════════════════════════════════════════════════════════════════
-- THM-POST-LINEAR-PATH-is-MONOTONE
-- Every additional fork reduces the Bule count by exactly 1.
-- ═══════════════════════════════════════════════════════════════════════

/-- Each additional stream from s to s+1 (when s < pathCount) reduces
    the Bule count by exactly 1.  The descent is uniform: one fork,
    one Bule saved, every step. -/
theorem each_fork_saves_one_bule
    {pathCount : ℕ} (_hPaths : 1 ≤ pathCount)
    (s : ℕ) (hs : 1 ≤ s) (_hsLt : s < pathCount) :
    topologicalDeficit pathCount s = topologicalDeficit pathCount (s + 1) + 1 := by
  unfold topologicalDeficit computationBeta1 transportBeta1
  omega

/-- The entire path from linear to frontier takes exactly pathCount - 1
    steps, each saving 1 Bule. -/
theorem path_length_equals_initial_bules
    {pathCount : ℕ} (hPaths : 1 ≤ pathCount) :
    topologicalDeficit pathCount 1 - topologicalDeficit pathCount pathCount = (pathCount : ℤ) - 1 := by
  have hStart := tcp_deficit_is_path_count_minus_one hPaths
  have hEnd := deficit_zero_at_match hPaths
  omega

/-- At any valid stream count between linearity and the frontier, the
    current Bule count is exactly the remaining distance to the frontier.
    The pessimism is not qualitative; it is an arithmetic gap. -/
theorem bule_count_equals_distance_to_frontier
    {pathCount s : ℕ}
    (hs : 1 ≤ s) (hLe : s ≤ pathCount) :
    topologicalDeficit pathCount s = (pathCount : ℤ) - s := by
  unfold topologicalDeficit computationBeta1 transportBeta1
  omega

/-- Any strict increase in diversity within the valid range strictly lowers
    the Bule count. The post-linear descent has no plateaus before the
    frontier. -/
theorem strict_descent_toward_frontier
    {pathCount s1 s2 : ℕ}
    (h1 : 1 ≤ s1) (h12 : s1 < s2) (h2 : s2 ≤ pathCount) :
    topologicalDeficit pathCount s2 < topologicalDeficit pathCount s1 := by
  have hs1 :
      topologicalDeficit pathCount s1 = (pathCount : ℤ) - s1 :=
    bule_count_equals_distance_to_frontier h1 (Nat.le_trans (Nat.le_of_lt h12) h2)
  have hs2 :
      topologicalDeficit pathCount s2 = (pathCount : ℤ) - s2 :=
    bule_count_equals_distance_to_frontier (by omega) h2
  omega

-- ═══════════════════════════════════════════════════════════════════════
-- THM-FRONTIER-is-GROUND-STATE
-- Zero Bules.  Cannot fold further.  Terminal.
-- ═══════════════════════════════════════════════════════════════════════

/-- At the frontier, the Bule count is 0. -/
theorem frontier_is_zero_bules
    {pathCount : ℕ} (hPaths : 1 ≤ pathCount) :
    topologicalDeficit pathCount pathCount = 0 := by
  exact deficit_zero_at_match hPaths

/-- On the valid stream range from linearity to the frontier, the Bule
    count is nonnegative. Beyond the frontier the integer-valued deficit
    may go negative, so the theorem does not overclaim. -/
theorem bule_count_nonnegative
    {pathCount streams : ℕ}
    (hs : 1 ≤ streams) (hLe : streams ≤ pathCount) :
    0 ≤ topologicalDeficit pathCount streams := by
  have hDeficit :
      topologicalDeficit pathCount streams = (pathCount : ℤ) - streams :=
    bule_count_equals_distance_to_frontier hs hLe
  omega

/-- Zero is the minimum Bule count.  The frontier is the ground state.
    Cannot go below zero on the valid path from linearity to the
    frontier.  Cannot fold further. -/
theorem zero_is_ground_state
    {pathCount : ℕ} (hPaths : 1 ≤ pathCount) :
    (∀ s : ℕ, 1 ≤ s → s ≤ pathCount →
      topologicalDeficit pathCount pathCount ≤ topologicalDeficit pathCount s) := by
  intro s hs hLe
  rw [frontier_is_zero_bules hPaths]
  exact bule_count_nonnegative hs hLe

/-- Within the valid stream range, having zero Bules is equivalent to
    already being at the frontier. There is no off-frontier zero-deficit
    state. -/
theorem zero_bules_iff_frontier
    {pathCount s : ℕ}
    (hs : 1 ≤ s) (hLe : s ≤ pathCount) :
    topologicalDeficit pathCount s = 0 ↔ s = pathCount := by
  constructor
  · intro hZero
    have hDeficit := bule_count_equals_distance_to_frontier hs hLe
    omega
  · intro hFrontier
    rw [hFrontier]
    exact frontier_is_zero_bules (by omega)

-- ═══════════════════════════════════════════════════════════════════════
-- THM-POST-LINEAR-TRANSITION-IRREVERSIBLE
-- Under rational agency, the first fork cannot be un-chosen.
-- ═══════════════════════════════════════════════════════════════════════

/-- Reverting from 2 streams to 1 stream strictly increases the Bule
    count.  Under any decision procedure that prefers fewer Bules
    (rational agency: less waste is preferred to more waste), this
    reversion is dominated and will not be chosen.

    The post-linear transition is a one-way door.  Not because the
    fold is physically irreversible (it is, but that is §19).
    Because the information that diversity reduces waste, once learned,
    makes monoculture a dominated strategy.  You cannot un-learn that
    two different is better than a hundred same. -/
theorem reversion_is_dominated
    {pathCount : ℕ} (hPaths : 2 ≤ pathCount) :
    topologicalDeficit pathCount 1 > topologicalDeficit pathCount 2 := by
  exact first_fork_strict_improvement hPaths

/-- Linear monoculture is not just a pessimum in the weak order; it is the
    unique strict worst case among all valid non-linear stream counts. -/
theorem linear_is_unique_strict_pessimum
    {pathCount s : ℕ}
    (_hPaths : 2 ≤ pathCount)
    (hs : 2 ≤ s) (hLe : s ≤ pathCount) :
    topologicalDeficit pathCount s < topologicalDeficit pathCount 1 := by
  exact strict_descent_toward_frontier (by omega) hs hLe

-- ═══════════════════════════════════════════════════════════════════════
-- THM-POST-LINEAR-WORLD: The conjunction
-- ═══════════════════════════════════════════════════════════════════════

/-- **THM-POST-LINEAR-WORLD**: The complete characterization.

    The linear world is the global pessimum.
    The first fork is a strict Pareto improvement.
    The path to zero Bules is monotone and uniform.
    The frontier is the ground state.
    Reversion is dominated.

    The post-linear world is not an aspiration.
    It is the unique rational destination. -/
theorem post_linear_world
    {pathCount : ℕ} (hPaths : 2 ≤ pathCount) :
    -- (1) Linear is pessimum
    (topologicalDeficit pathCount 1 = (pathCount : ℤ) - 1 ∧
     ∀ s : ℕ, 1 ≤ s → topologicalDeficit pathCount s ≤ topologicalDeficit pathCount 1) ∧
    -- (2) First fork is Pareto
    topologicalDeficit pathCount 2 < topologicalDeficit pathCount 1 ∧
    -- (3) Frontier is ground state
    topologicalDeficit pathCount pathCount = 0 ∧
    -- (4) Zero is minimum on the valid range
    (∀ s : ℕ, 1 ≤ s → s ≤ pathCount → 0 ≤ topologicalDeficit pathCount s) ∧
    -- (5) Reversion is dominated
    topologicalDeficit pathCount 1 > topologicalDeficit pathCount 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact linear_is_pessimum hPaths
  · exact first_fork_strict_improvement hPaths
  · exact frontier_is_zero_bules (by omega)
  · exact fun s hs hLe => bule_count_nonnegative hs hLe
  · exact reversion_is_dominated hPaths

end BuleyeanMath
