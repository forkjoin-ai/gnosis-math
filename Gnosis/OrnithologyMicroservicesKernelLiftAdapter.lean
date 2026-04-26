import Gnosis.GeometricErgodicity

namespace Gnosis

theorem ornithology_microservices_budget_yields_geometric_rate_certificate
    {birdCount sensorCost : Nat}
    (microserviceBudget : Nat)
    (_hBudget : birdCount + sensorCost = microserviceBudget) :
    ∃ rate : GeometricErgodicityRate,
      rate.rateNumerator = 3 ∧
      rate.rateDenominator = 4 ∧
      rate.initialBound = microserviceBudget + 1 := by
  have hEps1 : 0 < 1 := by decide
  have hEps2 : 0 < 2 := by decide
  have hM : 0 < microserviceBudget + 1 := by omega
  have hProd : 3 < 4 := by decide
  let rate := mkGeometricErgodicityRate 3 4 1 2 1 2 (microserviceBudget + 1)
                (by decide) (by decide) hProd hEps1 hEps2 hEps1 hEps2 hM
  exact ⟨rate, rfl, rfl, rfl⟩

structure OrnithologyMicroservicesKernelLiftAdapter
    (Ω : Type)
    (maxQueue : Nat) where
  birdCount : Nat
  sensorCost : Nat
  microserviceBudget : Nat
  _hBudget : birdCount + sensorCost = microserviceBudget
  embedding : DiscreteSubLatticeEmbedding Ω maxQueue
  witness : GeometricErgodicWitness maxQueue
  hKernelMatch : witness.envelope.kernel = embedding.discreteKernel

theorem ornithology_microservices_continuous_ergodicity_lift
    {Ω : Type}
    {maxQueue : Nat}
    (adapter : OrnithologyMicroservicesKernelLiftAdapter Ω maxQueue) :
    adapter.embedding.continuousKernel.fosterDrift ∧
    0 < adapter.embedding.continuousKernel.driftGap ∧
    adapter.witness.rate.rateNumerator < adapter.witness.rate.rateDenominator := by
  exact continuous_ergodicity_lift adapter.embedding adapter.witness adapter.hKernelMatch

end Gnosis
