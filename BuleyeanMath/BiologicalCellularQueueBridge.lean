namespace BuleyeanMath

structure BiologicalCellularQueueAssumptions where
  cellularDivisions : Nat
  queueServiceRate : Nat
  bridgeExact : cellularDivisions = queueServiceRate
  divisionsPositive : 0 < cellularDivisions

theorem biological_cellular_queue_bridge_exact
    (assumptions : BiologicalCellularQueueAssumptions) :
    0 < assumptions.cellularDivisions ->
    assumptions.cellularDivisions = assumptions.queueServiceRate ->
    0 < assumptions.queueServiceRate := by
  intro hPos hEq
  rw [←hEq]
  exact hPos

end BuleyeanMath