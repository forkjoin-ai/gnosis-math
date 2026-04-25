def EventHorizon : Type := Nat
def ZeroKnowledgeBoundary (e : EventHorizon) : Prop := e = e

theorem event_horizon_is_zkp_boundary (e : EventHorizon) : ZeroKnowledgeBoundary e := by
  rfl