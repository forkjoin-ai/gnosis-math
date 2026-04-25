namespace QueueTectonicSubductionUnitBoundary

structure TectonicQueue where
  subduction_rate : Nat
  queue_length : Nat
  boundary_condition : queue_length ≤ subduction_rate

theorem boundary_stability (q : TectonicQueue) :
  q.queue_length ≤ q.subduction_rate := by
  exact q.boundary_condition

end QueueTectonicSubductionUnitBoundary