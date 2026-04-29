namespace MoonshotSubductivePluralistThermodynamics

structure SubductivePluralistAdapter where
  tectonic_friction : Nat
  pluralist_nodes : Nat
  thermal_dissipation : Nat
  h_dissipation : thermal_dissipation = tectonic_friction + pluralist_nodes * tectonic_friction

theorem thermal_dissipation_bound (adapter : SubductivePluralistAdapter) :
  adapter.thermal_dissipation ≥ adapter.tectonic_friction := by
  rw [adapter.h_dissipation]
  exact Nat.le_add_right adapter.tectonic_friction (adapter.pluralist_nodes * adapter.tectonic_friction)

end MoonshotSubductivePluralistThermodynamics