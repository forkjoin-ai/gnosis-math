namespace MoonshotOracleToposFibration

structure ToposFibration where
  fibration : Prop
  resolves_stall : Prop

theorem fibration_resolves (t : ToposFibration) (h : t.fibration ∧ t.resolves_stall) : t.resolves_stall := h.right

end MoonshotOracleToposFibration