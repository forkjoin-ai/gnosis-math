namespace Gnosis

structure MissingLayerStabilizationAssumptions where
  layerMissing : Bool
  regularizationProvided : Bool
  stabilizationEnsured : layerMissing = true → regularizationProvided = true

theorem contrarian_missing_layer_stabilization (assumptions : MissingLayerStabilizationAssumptions) :
  assumptions.layerMissing = true → assumptions.regularizationProvided = true := by
  intro hMissing
  exact assumptions.stabilizationEnsured hMissing

end Gnosis