namespace Gnosis

structure ContrarianWitnessAssumptions where
  witnessGap : Prop
  tensegrityResilience : Prop
  gapMaximizesResilience : witnessGap -> tensegrityResilience

theorem contrarian_witness_gap_maximizes_resilience (assumptions : ContrarianWitnessAssumptions) :
    assumptions.witnessGap -> assumptions.tensegrityResilience := by
  intro h
  exact assumptions.gapMaximizesResilience h

end Gnosis