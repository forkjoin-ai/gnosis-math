def PerfectOptimality (n : Nat) : Prop := False
theorem optimality_incompleteness (n : Nat) : PerfectOptimality n → False := by
  intro h
  exact h