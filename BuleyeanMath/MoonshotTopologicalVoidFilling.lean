
namespace BuleyeanMath

structure TopologicalVoid where
  fillCapacity : Nat

theorem topological_void_fills (t : TopologicalVoid) (h : t.fillCapacity = 10) : t.fillCapacity ≥ 5 := by
  omega

end BuleyeanMath