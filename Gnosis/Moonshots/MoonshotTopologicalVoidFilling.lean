namespace Gnosis

structure TopologicalVoid where
  fillCapacity : Nat

theorem topological_void_fills (t : TopologicalVoid) (h : t.fillCapacity = 10) : t.fillCapacity ≥ 5 :=
  h ▸ Nat.le_add_right 5 5

end Gnosis