namespace BuleyeanMath

structure ContrarianExecutionIsLossAssumptions where
  oracleExecutionStalled : Prop
  executionIsLoss : Prop
  stallMeansExecutionLoss : oracleExecutionStalled -> executionIsLoss

theorem contrarian_execution_is_loss (assumptions : ContrarianExecutionIsLossAssumptions) :
    assumptions.oracleExecutionStalled -> assumptions.executionIsLoss := by
  intro hStalled
  exact assumptions.stallMeansExecutionLoss hStalled

end BuleyeanMath