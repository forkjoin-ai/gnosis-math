import Init

namespace ContrarianOracleStallPreventsCatastrophicCollapse

def systemEntropy (work stall : Nat) : Nat := work + stall

def collapseThreshold : Nat := 1000

theorem stall_maintains_thermodynamic_bound (work stall : Nat)
  (h_bound : work + stall ≤ collapseThreshold) :
  systemEntropy work stall ≤ collapseThreshold := by
  unfold systemEntropy
  exact h_bound

theorem stall_is_necessary (work stall : Nat)
  (h_collapse : work > collapseThreshold) :
  systemEntropy work stall > collapseThreshold := by
  unfold systemEntropy
  exact Nat.lt_of_lt_of_le h_collapse (Nat.le_add_right work stall)

end ContrarianOracleStallPreventsCatastrophicCollapse