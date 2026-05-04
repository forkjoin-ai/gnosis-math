namespace Gnosis

def structuredFrontier (frontier vented : Nat) : Nat := frontier - vented

def repairedFrontier (frontier vented repaired : Nat) : Nat :=
  structuredFrontier frontier vented + repaired

def frontierEntropyProxy (frontier : Nat) : Nat := frontier - 1

theorem structured_failure_conserves_frontier_mass {frontier vented : Nat}
    (hBound : vented <= frontier) :
    frontier = structuredFrontier frontier vented + vented := by
  unfold structuredFrontier
  exact (Nat.sub_add_cancel hBound).symm

theorem structured_failure_reduces_frontier_width {frontier vented : Nat}
    (hVented : 0 < vented)
    (hBound : vented <= frontier) :
    structuredFrontier frontier vented < frontier := by
  unfold structuredFrontier
  exact Nat.sub_lt (Nat.lt_of_lt_of_le hVented hBound) hVented

theorem structured_failure_reduces_entropy_proxy {frontier vented : Nat}
    (hVented : 0 < vented)
    (hSurvivor : vented < frontier) :
    frontierEntropyProxy (structuredFrontier frontier vented) <
      frontierEntropyProxy frontier := by
  unfold frontierEntropyProxy structuredFrontier
  -- (frontier - vented) - 1 < frontier - 1, since 1 ≤ frontier - vented < frontier.
  have hPos : 0 < frontier - vented := Nat.sub_pos_of_lt hSurvivor
  have hLt : frontier - vented < frontier :=
    Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) hSurvivor) hVented
  exact Nat.sub_lt_sub_right hPos hLt

theorem forked_frontier_collapses_to_single_survivor {frontier : Nat}
    (hForked : 1 < frontier) :
    structuredFrontier frontier (frontier - 1) = 1 := by
  unfold structuredFrontier
  exact Nat.sub_sub_self (Nat.le_of_lt hForked)

theorem success_from_forked_frontier_requires_failure {frontier vented : Nat}
    (hForked : 1 < frontier)
    (hCollapse : structuredFrontier frontier vented = 1) :
    0 < vented := by
  unfold structuredFrontier at hCollapse
  -- If vented = 0, then frontier = 1, contradicting 1 < frontier.
  rcases Nat.eq_zero_or_pos vented with hv0 | hvPos
  · exfalso
    rw [hv0, Nat.sub_zero] at hCollapse
    exact Nat.lt_irrefl 1 (hCollapse ▸ hForked)
  · exact hvPos

theorem single_survivor_has_zero_entropy_proxy {frontier : Nat}
    (hForked : 1 < frontier) :
    frontierEntropyProxy (structuredFrontier frontier (frontier - 1)) = 0 := by
  rw [forked_frontier_collapses_to_single_survivor hForked]
  unfold frontierEntropyProxy
  decide

theorem coupled_failure_preserves_or_increases_frontier_width
    {frontier vented repaired : Nat}
    (hBound : vented <= frontier)
    (hDebt : vented <= repaired) :
    frontier <= repairedFrontier frontier vented repaired := by
  unfold repairedFrontier structuredFrontier
  -- frontier = (frontier - vented) + vented ≤ (frontier - vented) + repaired.
  calc frontier
      = (frontier - vented) + vented := (Nat.sub_add_cancel hBound).symm
    _ ≤ (frontier - vented) + repaired := Nat.add_le_add_left hDebt _

theorem coupled_failure_preserves_or_increases_entropy_proxy
    {frontier vented repaired : Nat}
    (_hFrontier : 0 < frontier)
    (hBound : vented <= frontier)
    (hDebt : vented <= repaired) :
    frontierEntropyProxy frontier <=
      frontierEntropyProxy (repairedFrontier frontier vented repaired) := by
  unfold frontierEntropyProxy
  exact Nat.sub_le_sub_right
    (coupled_failure_preserves_or_increases_frontier_width hBound hDebt) 1

theorem coupled_failure_strictly_increases_entropy_proxy
    {frontier vented repaired : Nat}
    (hFrontier : 0 < frontier)
    (hBound : vented <= frontier)
    (hDebt : vented < repaired) :
    frontierEntropyProxy frontier <
      frontierEntropyProxy (repairedFrontier frontier vented repaired) := by
  -- frontier < (frontier - vented) + repaired, by frontier = (f-v) + v < (f-v) + repaired.
  have hLt : frontier < repairedFrontier frontier vented repaired := by
    show frontier < structuredFrontier frontier vented + repaired
    unfold structuredFrontier
    calc frontier
        = (frontier - vented) + vented := (Nat.sub_add_cancel hBound).symm
      _ < (frontier - vented) + repaired := Nat.add_lt_add_left hDebt _
  unfold frontierEntropyProxy
  exact Nat.sub_lt_sub_right hFrontier hLt

end Gnosis
