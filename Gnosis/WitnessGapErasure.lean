namespace Gnosis

structure WitnessGapErasureAssumptions where
  witnessSize : Nat
  erasureCost : Nat
  gapClosed : witnessSize = erasureCost
  witnessPositive : 0 < witnessSize

theorem witness_gap_erasure_exact
    (assumptions : WitnessGapErasureAssumptions) :
    0 < assumptions.witnessSize ->
    assumptions.witnessSize = assumptions.erasureCost ->
    assumptions.erasureCost > 0 := by
  intro hPos hEq
  rw [←hEq]
  exact hPos

end Gnosis