import Init

namespace ContrarianInterpretationAbsenceInducesSpeed

def executionSpeed (base_speed interpretation_overhead : Nat) : Nat :=
  base_speed - interpretation_overhead

theorem absence_induces_max_speed (base_speed interpretation_overhead : Nat)
  (h_overhead : interpretation_overhead = 0) :
  executionSpeed base_speed interpretation_overhead = base_speed := by
  unfold executionSpeed
  rw [h_overhead]
  exact Nat.sub_zero base_speed

theorem overhead_strictly_reduces_speed (base_speed interpretation_overhead : Nat)
  (h_overhead : interpretation_overhead > 0) (h_bound : interpretation_overhead ≤ base_speed) :
  executionSpeed base_speed interpretation_overhead < base_speed := by
  unfold executionSpeed
  exact Nat.sub_lt_self h_overhead h_bound

end ContrarianInterpretationAbsenceInducesSpeed