namespace BuleyeanMath

structure OracleStallAssumptions where
  executionSteps : Nat
  stallThreshold : Nat
  stallInevitable : executionSteps > stallThreshold

theorem oracle_execution_stall_obstruction
    (assumptions : OracleStallAssumptions) :
    assumptions.executionSteps > assumptions.stallThreshold ->
    assumptions.executionSteps ≠ assumptions.stallThreshold := by
  intro hGt
  exact ne_of_gt hGt

end BuleyeanMath