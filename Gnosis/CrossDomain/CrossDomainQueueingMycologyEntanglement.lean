namespace Gnosis

def queue_capacity (nodes : Nat) : Nat := nodes * 10
def mycelial_network_capacity (nodes : Nat) : Nat := nodes * 15

theorem mycology_dominates_queueing (n : Nat) (hn : n > 0) : queue_capacity n < mycelial_network_capacity n := by
  unfold queue_capacity mycelial_network_capacity
  -- Goal: n * 10 < n * 15. Rewrite 15 = 10 + 5, distribute, then add positive.
  rw [show (15 : Nat) = 10 + 5 from rfl, Nat.mul_add]
  exact Nat.lt_add_of_pos_right (Nat.mul_pos hn (by decide : 0 < 5))

end Gnosis