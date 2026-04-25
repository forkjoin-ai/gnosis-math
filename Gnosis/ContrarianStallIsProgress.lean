namespace Gnosis

structure ContrarianStallIsProgressAssumptions where
  oracleExecutionStalled : Prop
  progressMade : Prop
  stallIsProgress : oracleExecutionStalled -> progressMade

theorem contrarian_stall_is_progress (assumptions : ContrarianStallIsProgressAssumptions) :
    assumptions.oracleExecutionStalled -> assumptions.progressMade := by
  intro hStalled
  exact assumptions.stallIsProgress hStalled

end Gnosis