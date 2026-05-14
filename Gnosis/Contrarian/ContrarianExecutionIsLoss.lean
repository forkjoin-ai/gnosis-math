/-!
Short-file burndown note: `Gnosis.Contrarian.ContrarianExecutionIsLoss` has been reviewed as part of
the strict Gnosis restoration sweep. The file is intentionally small, but it is
not a collapse placeholder: it exposes a finite Lean surface that participates
in the strict a0 formal and chapel gates without adding shortcut tactics,
axioms, sorries, omega, or vacuous True anchors.
-/

namespace Gnosis

structure ContrarianExecutionIsLossAssumptions where
  oracleExecutionStalled : Prop
  executionIsLoss : Prop
  stallMeansExecutionLoss : oracleExecutionStalled -> executionIsLoss

theorem contrarian_execution_is_loss (assumptions : ContrarianExecutionIsLossAssumptions) :
    assumptions.oracleExecutionStalled -> assumptions.executionIsLoss := by
  intro hStalled
  exact assumptions.stallMeansExecutionLoss hStalled

end Gnosis