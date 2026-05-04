import Gnosis.DeficitCapacity

namespace Gnosis

/-!
# The American Frontier

The frontier is the first point where transport capacity matches the path
count. Before that point there is positive deficit; at the frontier the
deficit closes to zero; beyond it there is no positive deficit left to close.
-/

/-- The frontier is the exact stream count needed to match the path count. -/
def frontierStreamCount (pathCount : Nat) : Nat :=
  pathCount

/-- Being at the frontier means using exactly the frontier stream count. -/
def AtFrontier (pathCount streams : Nat) : Prop :=
  streams = frontierStreamCount pathCount

/-- The frontier closes the topological deficit exactly. -/
theorem frontier_closes_deficit
    {pathCount : Nat}
    (hPaths : 1 ≤ pathCount) :
    topologicalDeficit pathCount (frontierStreamCount pathCount) = 0 := by
  simpa [frontierStreamCount] using matched_deficit_is_zero hPaths

/-- Any single-stream transport below a nontrivial path count sits before the frontier. -/
theorem single_stream_is_pre_frontier
    {pathCount : Nat}
    (hPaths : 2 ≤ pathCount) :
    ¬ AtFrontier pathCount 1 := by
  unfold AtFrontier frontierStreamCount
  exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide : (1 : Nat) < 2) hPaths)

/-- Before the frontier, a single stream carries a positive deficit. -/
theorem pre_frontier_single_stream_has_positive_deficit
    {pathCount : Nat}
    (hPaths : 2 ≤ pathCount) :
    0 < topologicalDeficit pathCount 1 := by
  exact single_stream_deficit_positive hPaths

/-- Increasing stream count toward the frontier never increases deficit. -/
theorem frontier_progress_monotone
    {pathCount s : Nat}
    (hBase : 1 ≤ s)
    (hProgress : s ≤ frontierStreamCount pathCount) :
    topologicalDeficit pathCount (frontierStreamCount pathCount) ≤
      topologicalDeficit pathCount s := by
  simpa [frontierStreamCount] using deficit_monotone_in_streams hBase hProgress

/-- The frontier has strictly less deficit than a single-stream transport when paths fork. -/
theorem frontier_strictly_improves_on_single_stream
    {pathCount : Nat}
    (hPaths : 2 ≤ pathCount) :
    topologicalDeficit pathCount (frontierStreamCount pathCount) <
      topologicalDeficit pathCount 1 := by
  have hFrontier : topologicalDeficit pathCount (frontierStreamCount pathCount) = 0 := by
    exact frontier_closes_deficit (Nat.le_trans (by decide) hPaths)
  have hSingle : 0 < topologicalDeficit pathCount 1 := by
    exact pre_frontier_single_stream_has_positive_deficit hPaths
  rw [hFrontier]
  exact hSingle

/-- Once the frontier is reached, adding more streams cannot create a positive deficit. -/
theorem post_frontier_has_no_positive_deficit
    {pathCount streams : Nat}
    (hCover : frontierStreamCount pathCount ≤ streams) :
    topologicalDeficit pathCount streams ≤ 0 := by
  simpa [frontierStreamCount] using deficit_nonpositive_when_streams_cover_paths hCover

end Gnosis
