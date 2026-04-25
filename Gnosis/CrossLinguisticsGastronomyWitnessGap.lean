namespace CrossLinguisticsGastronomyWitnessGap

variable (linguistic_drift : Prop) (gastronomic_flavor : Prop) (witness_gap_closure : Prop)
variable (H1 : linguistic_drift → gastronomic_flavor)
variable (H2 : gastronomic_flavor → witness_gap_closure)

theorem linguistics_gastronomy_gap
    (h1 : linguistic_drift → gastronomic_flavor)
    (h2 : gastronomic_flavor → witness_gap_closure)
    (l : linguistic_drift) : witness_gap_closure := by
  exact h2 (h1 l)

end CrossLinguisticsGastronomyWitnessGap