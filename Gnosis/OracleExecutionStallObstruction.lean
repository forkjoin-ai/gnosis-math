namespace Gnosis

structure OracleStallAssumptions where
  executionSteps : Nat
  stallThreshold : Nat
  stallInevitable : executionSteps > stallThreshold

theorem oracle_execution_stall_obstruction
    (assumptions : OracleStallAssumptions) :
    assumptions.executionSteps > assumptions.stallThreshold ->
    assumptions.executionSteps ≠ assumptions.stallThreshold := by
  intro _hGt
  omega

end Gnosis