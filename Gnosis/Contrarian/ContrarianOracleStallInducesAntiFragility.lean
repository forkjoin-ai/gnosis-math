namespace ContrarianOracleStallInducesAntiFragility

variable (oracle_execution_stall : Prop) (anti_fragility : Prop)
variable (H : oracle_execution_stall → anti_fragility)

theorem stall_is_anti_fragile
    (h : oracle_execution_stall → anti_fragility)
    (o : oracle_execution_stall) : anti_fragility := by
  exact h o

end ContrarianOracleStallInducesAntiFragility