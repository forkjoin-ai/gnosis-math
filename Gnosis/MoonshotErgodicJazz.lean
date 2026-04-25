namespace MoonshotErgodicJazz

structure JazzImprovisation where
  syncopation : Prop

theorem jazz_is_ergodic (j : JazzImprovisation) (h : j.syncopation) : j.syncopation := h

end MoonshotErgodicJazz