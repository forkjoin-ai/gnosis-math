import Gnosis.AmericanFrontier
import Gnosis.DeficitCapacity

namespace Gnosis

/-!
# THM-DIVERSITY-OPTIMALITY: The Diversity Theorem

The simple model is honest:

- path count is the computational demand,
- stream count is the transport-side diversity,
- `topologicalDeficit` measures the remaining mismatch.

Under that model, more diversity helps until the frontier is reached, where
the deficit closes to zero. Additional diversity beyond the frontier does not
reintroduce positive deficit.
-/

/-- A stream count is diverse when it has moved beyond the single-stream line. -/
def Diverse (streams : Nat) : Prop :=
  2 ≤ streams

/-- Before the frontier, adding one stream strictly decreases deficit. -/
theorem added_diversity_strictly_reduces_deficit
    {pathCount streams : Nat}
    (hBase : 1 ≤ streams)
    (_hBelow : streams < pathCount) :
    topologicalDeficit pathCount (streams + 1) <
      topologicalDeficit pathCount streams := by
  unfold topologicalDeficit computationComplexity transportCapacity
  omega

/-- The first fork strictly improves on the single-stream transport. -/
theorem first_fork_improves_deficit
    {pathCount : Nat}
    (hPaths : 2 ≤ pathCount) :
    topologicalDeficit pathCount 2 < topologicalDeficit pathCount 1 := by
  exact added_diversity_strictly_reduces_deficit (by decide) hPaths

/-- Any stream count below the frontier still leaves positive deficit. -/
theorem below_frontier_deficit_positive
    {pathCount streams : Nat}
    (hBase : 1 ≤ streams)
    (hBelow : streams < pathCount) :
    0 < topologicalDeficit pathCount streams := by
  unfold topologicalDeficit computationComplexity transportCapacity
  omega

/-- Reaching the frontier closes the deficit exactly. -/
theorem frontier_is_optimal
    {pathCount : Nat}
    (hPaths : 1 ≤ pathCount) :
    topologicalDeficit pathCount (frontierStreamCount pathCount) = 0 := by
  exact frontier_closes_deficit hPaths

/-- Beyond the frontier there is no positive deficit left to eliminate. -/
theorem post_frontier_is_nonpositive
    {pathCount streams : Nat}
    (hCover : frontierStreamCount pathCount ≤ streams) :
    topologicalDeficit pathCount streams ≤ 0 := by
  exact post_frontier_has_no_positive_deficit hCover

/-- Optimal diversity is the point where deficit reaches zero for the first time. -/
theorem frontier_is_first_zero_deficit_point
    {pathCount streams : Nat}
    (hBase : 1 ≤ streams)
    (hBelow : streams < frontierStreamCount pathCount) :
    topologicalDeficit pathCount streams ≠ 0 := by
  have hPositive : 0 < topologicalDeficit pathCount streams := by
    simpa [frontierStreamCount] using below_frontier_deficit_positive hBase hBelow
  omega

/-- Diversity improves monotonically toward the frontier. -/
theorem diversity_progress_monotone
    {pathCount s1 s2 : Nat}
    (hBase : 1 ≤ s1)
    (hOrder : s1 ≤ s2)
    (_hBound : s2 ≤ frontierStreamCount pathCount) :
    topologicalDeficit pathCount s2 ≤ topologicalDeficit pathCount s1 := by
  exact deficit_monotone_in_streams hBase hOrder

/-- The frontier strictly dominates the single-stream line for any nontrivial path count. -/
theorem frontier_dominates_linear_world
    {pathCount : Nat}
    (hPaths : 2 ≤ pathCount) :
    topologicalDeficit pathCount (frontierStreamCount pathCount) <
      topologicalDeficit pathCount 1 := by
  exact frontier_strictly_improves_on_single_stream hPaths

end Gnosis
