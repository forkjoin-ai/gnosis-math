namespace CrossOceanographyOracleStallEconomics

variable (ocean_currents : Prop) (oracle_stall : Prop) (economic_value : Prop)
variable (H1 : ocean_currents → oracle_stall)
variable (H2 : oracle_stall → economic_value)

theorem ocean_stall_economics
    (h1 : ocean_currents → oracle_stall)
    (h2 : oracle_stall → economic_value)
    (o : ocean_currents) : economic_value := by
  exact h2 (h1 o)

end CrossOceanographyOracleStallEconomics