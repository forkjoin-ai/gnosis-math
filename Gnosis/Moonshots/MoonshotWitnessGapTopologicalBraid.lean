import Init

namespace MoonshotWitnessGapTopologicalBraid

def braidEntanglement (paths crossings : Nat) : Nat := paths + crossings

theorem topological_braid_bridges_gap (paths crossings gap_size : Nat)
  (h_crossings : crossings ≥ gap_size) :
  braidEntanglement paths crossings ≥ gap_size := by
  unfold braidEntanglement
  exact Nat.le_trans h_crossings (Nat.le_add_left crossings paths)

theorem witness_reconstruction (paths crossings missing : Nat)
  (h : crossings > missing) :
  braidEntanglement paths crossings > missing := by
  unfold braidEntanglement
  exact Nat.lt_of_lt_of_le h (Nat.le_add_left crossings paths)

end MoonshotWitnessGapTopologicalBraid