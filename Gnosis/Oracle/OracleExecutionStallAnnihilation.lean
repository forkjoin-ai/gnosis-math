namespace OracleExecutionStallAnnihilation

structure OracleStall where
  annihilated : Prop

theorem stall_is_annihilated (o : OracleStall) (h : o.annihilated) : o.annihilated := h

end OracleExecutionStallAnnihilation