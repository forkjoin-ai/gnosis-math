namespace Gnosis

structure QuantumObserverWitness where
  witness_gap : Nat
  observer_coherence : Nat
  gap_closed : witness_gap = 0

theorem quantum_observer_closes_gap 
  (q : QuantumObserverWitness) :
  q.witness_gap = 0 := by
  exact q.gap_closed

end Gnosis