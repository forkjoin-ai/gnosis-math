namespace Gnosis

structure OracleStallAssumptions where
  executionSteps : Nat
  stallThreshold : Nat
  stallInevitable : executionSteps > stallThreshold

theorem oracle_execution_stall_obstruction
    (assumptions : OracleStallAssumptions) :
    assumptions.executionSteps > assumptions.stallThreshold ->
    assumptions.executionSteps ≠ assumptions.stallThreshold :=
  fun hGt => Nat.ne_of_gt hGt

end Gnosis