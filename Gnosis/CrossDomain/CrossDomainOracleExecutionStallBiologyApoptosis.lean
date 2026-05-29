namespace Gnosis

structure BiologicalApoptosis where
  stall_toxicity : Nat
  apoptosis_threshold : Nat
  triggers_recovery : stall_toxicity ≥ apoptosis_threshold

theorem stall_triggers_apoptosis (b : BiologicalApoptosis) :
    b.stall_toxicity ≥ b.apoptosis_threshold := by
  exact b.triggers_recovery

end Gnosis