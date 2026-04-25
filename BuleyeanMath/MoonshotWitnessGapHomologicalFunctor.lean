namespace MoonshotWitnessGapHomologicalFunctor

variable (witness_gap : Prop) (homological_functor_resolution : Prop)
variable (H : witness_gap → homological_functor_resolution)

theorem homological_functor_bypass
    (h : witness_gap → homological_functor_resolution)
    (w : witness_gap) : homological_functor_resolution := by
  exact h w

end MoonshotWitnessGapHomologicalFunctor