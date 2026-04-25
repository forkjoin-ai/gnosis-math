namespace MoonshotChronologicalVoidShatter

structure VoidShatterAdapter where
  void_density : Nat
  chronological_pressure : Nat
  shatter_horizon : Nat
  h_shatter : shatter_horizon = void_density * chronological_pressure + void_density

theorem void_shatter_density_bound (adapter : VoidShatterAdapter) :
  adapter.shatter_horizon ≥ adapter.void_density := by
  rw [adapter.h_shatter]
  exact Nat.le_add_left adapter.void_density (adapter.void_density * adapter.chronological_pressure)

end MoonshotChronologicalVoidShatter