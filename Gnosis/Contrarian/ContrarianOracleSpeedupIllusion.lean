namespace Gnosis

structure OracleSpeedupIllusionAssumptions where
  speedOptimized : Bool
  interpretationMissing : Bool
  convergenceDecreased : speedOptimized = true ∧ interpretationMissing = true → True

theorem contrarian_oracle_speedup_illusion (assumptions : OracleSpeedupIllusionAssumptions) :
  assumptions.speedOptimized = true → assumptions.interpretationMissing = true →
    assumptions.speedOptimized = true ∧ assumptions.interpretationMissing = true := by
  intro h1 h2
  exact ⟨h1, h2⟩

end Gnosis
