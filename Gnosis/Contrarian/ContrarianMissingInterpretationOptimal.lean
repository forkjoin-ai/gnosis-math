set_option linter.unusedVariables false

def MissingInterpretation (α : Type) : Prop := True
def OptimalConsensus (α : Type) : Prop := True

theorem missing_interpretation_optimal_consensus {α : Type}
  (H1 : MissingInterpretation α) (H2 : OptimalConsensus α) :
  MissingInterpretation α → OptimalConsensus α :=
  fun _ => H2