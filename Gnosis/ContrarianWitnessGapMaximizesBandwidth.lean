namespace ContrarianWitnessGapMaximizesBandwidth

variable (witness_gap : Prop) (maximum_bandwidth : Prop)
variable (H : witness_gap → maximum_bandwidth)

theorem witness_gap_bandwidth
    (h : witness_gap → maximum_bandwidth)
    (w : witness_gap) : maximum_bandwidth := by
  exact h w

end ContrarianWitnessGapMaximizesBandwidth