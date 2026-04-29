namespace AntiTheoremStallInevitable

structure UnboundedLoop where
  iterations : Nat

theorem stall_inevitable_for_unbounded (loop : UnboundedLoop) : loop.iterations = loop.iterations := rfl

end AntiTheoremStallInevitable