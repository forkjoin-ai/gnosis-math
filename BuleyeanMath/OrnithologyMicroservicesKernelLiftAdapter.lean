import BuleyeanMath.GeometricErgodicity

namespace BuleyeanMath

theorem ornithology_microservices_budget_yields_geometric_rate_certificate
    {birdCount sensorCost : Nat}
    (microserviceBudget : Nat)
    (_hBudget : birdCount + sensorCost = microserviceBudget) :
    ∃ rate : GeometricErgodicityRate,
      rate.contractionRate = 3 / 4 ∧
      rate.initialBound = microserviceBudget + 1 := by
  have hEps1 : 0 < (1 / 2 : ℝ) := by norm_num
  have hEps2 : 0 < (1 / 2 : ℝ) := by norm_num
  have hM : 0 < (microserviceBudget + 1 : ℝ) := by positivity
  have hProd : (1 / 2 : ℝ) * (1 / 2 : ℝ) < 1 := by norm_num
  let rate := mkGeometricErgodicityRate (1 / 2) (1 / 2) (microserviceBudget + 1) hEps1 hEps2 hM hProd
  use rate
  constructor
  · show 1 - (1 / 2 : ℝ) * (1 / 2 : ℝ) = 3 / 4
    norm_num
  · rfl

structure OrnithologyMicroservicesKernelLiftAdapter
    (Ω : Type*) [MeasurableSpace Ω] [TopologicalSpace Ω]
    (maxQueue : ℕ) where
  birdCount : Nat
  sensorCost : Nat
  microserviceBudget : Nat
  _hBudget : birdCount + sensorCost = microserviceBudget
  budgetReal : ℝ
  _hBudgetRealEq : budgetReal = microserviceBudget
  embedding : DiscreteSubLatticeEmbedding Ω maxQueue
  witness : GeometricErgodicWitness maxQueue
  hKernelMatch : witness.envelope.kernel = embedding.discreteKernel

theorem ornithology_microservices_continuous_ergodicity_lift
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    {maxQueue : ℕ}
    (adapter : OrnithologyMicroservicesKernelLiftAdapter Ω maxQueue) :
    adapter.embedding.continuousKernel.fosterDrift ∧
    0 < adapter.embedding.continuousKernel.driftGap ∧
    adapter.witness.rate.contractionRate < 1 := by
  exact continuous_ergodicity_lift adapter.embedding adapter.witness adapter.hKernelMatch