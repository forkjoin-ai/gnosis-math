namespace BuleyeanMath

structure WitnessGapSecurity where
  gap_size : Nat
  adversarial_induction_cost : Nat
  is_secure : adversarial_induction_cost > gap_size

theorem witness_gap_increases_cost (w : WitnessGapSecurity) :
    w.adversarial_induction_cost > w.gap_size := by
  exact w.is_secure

end BuleyeanMath