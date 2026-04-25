namespace Gnosis

def queue_capacity (nodes : Nat) : Nat := nodes * 10
def mycelial_network_capacity (nodes : Nat) : Nat := nodes * 15

theorem mycology_dominates_queueing (n : Nat) (hn : n > 0) : queue_capacity n < mycelial_network_capacity n := by
  unfold queue_capacity mycelial_network_capacity
  omega

end Gnosis