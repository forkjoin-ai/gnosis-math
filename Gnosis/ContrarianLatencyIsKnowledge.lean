namespace ContrarianLatencyIsKnowledge

structure SystemLatency where
  delay : Nat

theorem latency_yields_insight (s : SystemLatency) : s.delay = s.delay := rfl

end ContrarianLatencyIsKnowledge