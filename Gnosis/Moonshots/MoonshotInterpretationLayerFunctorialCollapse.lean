namespace ForkRaceFold

structure InterpretationManifold where
  dimension : Nat
  collapsed_dimension : Nat

theorem functorial_collapse_reduces_dim (m : InterpretationManifold) (h : m.collapsed_dimension = m.dimension / 2) (h_dim : m.dimension > 1) :
  m.collapsed_dimension < m.dimension :=
  -- Init-only term mode: `h_dim : 1 < m.dimension` ⇒ `0 < m.dimension` via
  -- `Nat.zero_lt_of_lt`. `Nat.lt_succ_self 1 : 1 < 2`. `Nat.div_lt_self`
  -- (Init core) closes `m.dimension / 2 < m.dimension`. `h ▸ ·` rewrites
  -- `m.collapsed_dimension` ↦ `m.dimension / 2` in the goal.
  h ▸ Nat.div_lt_self (Nat.zero_lt_of_lt h_dim) (Nat.lt_succ_self 1)

end ForkRaceFold