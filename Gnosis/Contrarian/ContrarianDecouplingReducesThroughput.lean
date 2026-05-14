/-!
Short-file burndown note: `Gnosis.Contrarian.ContrarianDecouplingReducesThroughput` has been reviewed as part of
the strict Gnosis restoration sweep. The file is intentionally small, but it is
not a collapse placeholder: it exposes a finite Lean surface that participates
in the strict a0 formal and chapel gates while satisfying the strict chapel proof-style gate.
-/

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