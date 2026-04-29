namespace Gnosis

structure MissingInterpretation where
  entropy_transfer : Nat
  interpretation_overhead : Nat
  optimal_transfer : entropy_transfer > interpretation_overhead

theorem missing_layer_is_optimal (m : MissingInterpretation) :
    m.entropy_transfer > m.interpretation_overhead := by
  exact m.optimal_transfer

end Gnosis