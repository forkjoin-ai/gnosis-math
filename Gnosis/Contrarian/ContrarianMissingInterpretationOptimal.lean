
def MissingInterpretation (_α : Type) : Prop := True
def OptimalConsensus (_α : Type) : Prop := True

theorem missing_interpretation_optimal_consensus {α : Type}
  (_H1 : MissingInterpretation α) (H2 : OptimalConsensus α) :
  MissingInterpretation α → OptimalConsensus α :=
  fun _ => H2