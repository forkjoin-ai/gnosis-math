namespace ContrarianDecouplingReducesThroughput

structure DecouplingThroughputAdapter where
  component_decoupling : Nat
  communication_overhead : Nat
  throughput_bottleneck : Nat
  h_bottleneck : throughput_bottleneck = component_decoupling + communication_overhead

theorem bottleneck_bound (adapter : DecouplingThroughputAdapter) :
  adapter.throughput_bottleneck ≥ adapter.component_decoupling := by
  rw [adapter.h_bottleneck]
  exact Nat.le_add_right adapter.component_decoupling adapter.communication_overhead

end ContrarianDecouplingReducesThroughput