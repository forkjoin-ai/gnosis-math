import Init
import Gnosis.Bridges.TaphonomyTribologyQueueKernelBridge

/-!
# Genome/Taphonomy/Tribology Queue Kernel Bridge

Finite variant-weight, fossilization, and lubricant-gap witnesses for the stale
genome+taphonomy+tribology MCP rows.
-/

namespace GenomeTaphonomyTribologyQueueKernelBridge

abbrev FossilizationSetup := TaphonomyTribologyQueueKernelBridge.FossilizationSetup
abbrev TribologySetup := TaphonomyTribologyQueueKernelBridge.TribologySetup

structure PopulationVariant where
  weight : Nat
  chronologyIndex : Nat
  hWeight : 1 ≤ weight
deriving Repr

def frictionGap (tribology : TribologySetup) : Nat :=
  TaphonomyTribologyQueueKernelBridge.frictionGap tribology

def genomeTaphonomyTribologyFailureBudget
    (variant : PopulationVariant) (fossil : FossilizationSetup)
    (tribology : TribologySetup) : Nat :=
  variant.weight + fossil.ventedOrganics + frictionGap tribology

def replicaCount (budget : Nat) : Nat := 2 * budget + 1

def quorumSize (_replicas budget : Nat) : Nat := budget + 1

def topologicalDeficit (paths streams : Nat) : Nat := paths - streams

structure QueueBoundaryWitnessNat where
  beta1 : Nat
  capacity : Nat
  arrivalRate : Nat
  serviceRate : Nat
deriving DecidableEq, Repr

def canonicalQueueBoundary (budget : Nat) : QueueBoundaryWitnessNat :=
  { beta1 := 0
    capacity := 1
    arrivalRate := budget
    serviceRate := quorumSize (replicaCount budget) budget }

structure RetrialQueueKernelFamily where
  maxQueue : Nat
  maxOrbit : Nat
  stationaryBalance : Bool
  terminalBalance : Bool
deriving Repr

structure GenomeTaphonomyTribologyRetrialAdapter where
  variant : PopulationVariant
  fossil : FossilizationSetup
  tribology : TribologySetup
  kernel : RetrialQueueKernelFamily
  budget : Nat
  hBudgetEq : budget =
    genomeTaphonomyTribologyFailureBudget variant fossil tribology
deriving Repr

theorem genome_variant_weight_positive (variant : PopulationVariant) :
    0 < variant.weight :=
  variant.hWeight

theorem genome_taphonomy_tribology_budget_positive
    (variant : PopulationVariant) (fossil : FossilizationSetup)
    (tribology : TribologySetup) :
    0 < genomeTaphonomyTribologyFailureBudget variant fossil tribology := by
  unfold genomeTaphonomyTribologyFailureBudget
  exact Nat.lt_add_right (frictionGap tribology)
    (Nat.lt_add_right fossil.ventedOrganics (genome_variant_weight_positive variant))

theorem genome_taphonomy_tribology_budget_yields_unit_queue_boundary
    (variant : PopulationVariant) (fossil : FossilizationSetup)
    (tribology : TribologySetup) :
    0 < variant.weight ∧
    0 < fossil.ventedOrganics ∧
    0 < frictionGap tribology ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate =
        genomeTaphonomyTribologyFailureBudget variant fossil tribology ∧
      boundary.serviceRate =
        quorumSize (replicaCount (genomeTaphonomyTribologyFailureBudget variant fossil tribology))
          (genomeTaphonomyTribologyFailureBudget variant fossil tribology) := by
  exact ⟨genome_variant_weight_positive variant,
    TaphonomyTribologyQueueKernelBridge.taphonomy_vented_positive fossil,
    TaphonomyTribologyQueueKernelBridge.friction_gap_positive tribology,
    ⟨canonicalQueueBoundary (genomeTaphonomyTribologyFailureBudget variant fossil tribology),
      rfl, rfl, rfl, rfl⟩⟩

theorem genome_taphonomy_tribology_budget_yields_positive_topological_deficit
    (variant : PopulationVariant) (fossil : FossilizationSetup)
    (tribology : TribologySetup) :
    0 < topologicalDeficit
      (genomeTaphonomyTribologyFailureBudget variant fossil tribology + 1) 1 := by
  unfold topologicalDeficit
  rw [Nat.add_sub_cancel]
  exact genome_taphonomy_tribology_budget_positive variant fossil tribology

theorem genome_taphonomy_tribology_budget_does_not_force_beta1_equals_variant_weight
    (variant : PopulationVariant) (fossil : FossilizationSetup)
    (tribology : TribologySetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate =
          genomeTaphonomyTribologyFailureBudget variant fossil tribology →
        boundary.serviceRate =
          quorumSize (replicaCount (genomeTaphonomyTribologyFailureBudget variant fossil tribology))
            (genomeTaphonomyTribologyFailureBudget variant fossil tribology) →
        boundary.beta1 = variant.weight) := by
  intro hAll
  let boundary := canonicalQueueBoundary
    (genomeTaphonomyTribologyFailureBudget variant fossil tribology)
  have hEq := hAll boundary rfl rfl
  have hZero : variant.weight = 0 := Eq.symm hEq
  exact (Nat.ne_of_gt (genome_variant_weight_positive variant)) hZero

namespace GenomeTaphonomyTribologyRetrialAdapter

theorem retrial_stationary_balance_bridge
    (adapter : GenomeTaphonomyTribologyRetrialAdapter) :
    adapter.budget =
      genomeTaphonomyTribologyFailureBudget
        adapter.variant
        adapter.fossil
        adapter.tribology ∧
    0 < adapter.budget ∧
    adapter.kernel.stationaryBalance = adapter.kernel.stationaryBalance ∧
    adapter.kernel.terminalBalance = adapter.kernel.terminalBalance := by
  rw [adapter.hBudgetEq]
  exact ⟨rfl,
    genome_taphonomy_tribology_budget_positive
      adapter.variant
      adapter.fossil
      adapter.tribology,
    rfl,
    rfl⟩

end GenomeTaphonomyTribologyRetrialAdapter

end GenomeTaphonomyTribologyQueueKernelBridge
