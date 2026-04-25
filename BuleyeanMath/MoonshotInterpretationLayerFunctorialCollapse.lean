
namespace ForkRaceFold

structure InterpretationManifold where
  dimension : Nat
  collapsed_dimension : Nat

theorem functorial_collapse_reduces_dim (m : InterpretationManifold) (h : m.collapsed_dimension = m.dimension / 2) (h_dim : m.dimension > 1) :
  m.collapsed_dimension < m.dimension := by
  omega

end ForkRaceFold