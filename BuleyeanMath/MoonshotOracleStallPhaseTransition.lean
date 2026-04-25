namespace BuleyeanMath

structure StallPhaseTransition where
  stall_duration : Nat
  phase_shift_threshold : Nat
  is_transitioning : stall_duration ≥ phase_shift_threshold

theorem oracle_stall_is_phase_shift (p : StallPhaseTransition) :
    p.stall_duration ≥ p.phase_shift_threshold := by
  exact p.is_transitioning

end BuleyeanMath