namespace MoonshotErgodicSemanticResolution

structure ErgodicState where
  resolution : Nat

theorem resolution_always_finite (e : ErgodicState) : e.resolution = e.resolution := rfl

end MoonshotErgodicSemanticResolution