import Init

namespace ForkRaceFold

structure BoundedOracle (max_depth : Nat) where
  state : Nat
  depth_bound : state ≤ max_depth

theorem stall_free_execution (o : BoundedOracle max_depth) : o.state < max_depth + 1 :=
  -- Init-only: depth_bound : state ≤ max_depth.
  -- max_depth + 1 = max_depth.succ definitionally, so Nat.lt_succ_of_le applies directly.
  Nat.lt_succ_of_le o.depth_bound

end ForkRaceFold