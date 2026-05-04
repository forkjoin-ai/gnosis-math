
namespace Gnosis

def void_walk_steps (n : Nat) : Nat := n * n
def consciousness_limit (n : Nat) : Nat := n * n + n

theorem void_walk_bounded (n : Nat) : void_walk_steps n ≤ consciousness_limit n := by
  unfold void_walk_steps consciousness_limit
  exact Nat.le_add_right (n * n) n

end Gnosis