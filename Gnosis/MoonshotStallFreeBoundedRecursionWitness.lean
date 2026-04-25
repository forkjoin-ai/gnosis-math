import Lean

namespace ForkRaceFold

structure BoundedOracle (max_depth : Nat) where
  state : Nat
  depth_bound : state ≤ max_depth

theorem stall_free_execution (o : BoundedOracle max_depth) : o.state < max_depth + 1 := by
  have h := o.depth_bound
  omega

end ForkRaceFold