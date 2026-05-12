import Init

/-!
# Topological Contagion + Technique Queue Bridge

Finite queue witnesses for contagion spillover combined with a technique
altitude budget.
-/

namespace TopologicalContagionTechniqueQueueKernelBridge

structure ContagionSource where
  internalHeat : Nat
  containmentThreshold : Nat
  hSpills : containmentThreshold < internalHeat
deriving Repr

structure NeighborLoad where
  phantomLoad : Nat
deriving Repr

structure TechniqueWitness where
  altitude : Nat
deriving Repr

def spilloverLoad (source : ContagionSource) : Nat :=
  source.internalHeat - source.containmentThreshold

def contagionTechniqueBudget
    (neighbor : NeighborLoad)
    (technique : TechniqueWitness) : Nat :=
  neighbor.phantomLoad + technique.altitude

def replicaCount (budget : Nat) : Nat := 2 * budget + 1

def quorumSize (_replicas budget : Nat) : Nat := budget + 1

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

structure GeometricRateNat where
  numerator : Nat
  denominator : Nat
  initialBound : Nat
  hRateLtOne : numerator < denominator
  hDenomPos : 0 < denominator
  hInitialBoundPos : 0 < initialBound
deriving Repr

def budgetGeometricRate (budget : Nat) : GeometricRateNat :=
  { numerator := 3
    denominator := 4
    initialBound := budget + 1
    hRateLtOne := by decide
    hDenomPos := by decide
    hInitialBoundPos := Nat.succ_pos budget }

theorem contagion_technique_budget_yields_unit_queue_boundary
    (source : ContagionSource)
    (neighbor : NeighborLoad)
    (technique : TechniqueWitness)
    (hCoupled : spilloverLoad source ≤ neighbor.phantomLoad) :
    spilloverLoad source ≤ neighbor.phantomLoad ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = contagionTechniqueBudget neighbor technique ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (contagionTechniqueBudget neighbor technique))
          (contagionTechniqueBudget neighbor technique) := by
  exact ⟨hCoupled,
    ⟨canonicalQueueBoundary (contagionTechniqueBudget neighbor technique),
      rfl, rfl, rfl, rfl⟩⟩

theorem contagion_technique_budget_does_not_force_beta1_equals_budget
    (neighbor : NeighborLoad)
    (technique : TechniqueWitness)
    (hPositive : 0 < contagionTechniqueBudget neighbor technique) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = contagionTechniqueBudget neighbor technique →
        boundary.serviceRate =
          quorumSize
            (replicaCount (contagionTechniqueBudget neighbor technique))
            (contagionTechniqueBudget neighbor technique) →
        boundary.beta1 = contagionTechniqueBudget neighbor technique) := by
  intro hAll
  let boundary := canonicalQueueBoundary (contagionTechniqueBudget neighbor technique)
  have hEq : boundary.beta1 = contagionTechniqueBudget neighbor technique :=
    hAll boundary rfl rfl
  rw [show boundary.beta1 = 0 by rfl] at hEq
  rw [← hEq] at hPositive
  exact Nat.lt_irrefl 0 hPositive

theorem contagion_technique_budget_yields_geometric_rate_certificate
    (neighbor : NeighborLoad)
    (technique : TechniqueWitness) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (contagionTechniqueBudget neighbor technique) ∧
      rate.initialBound = contagionTechniqueBudget neighbor technique + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨budgetGeometricRate (contagionTechniqueBudget neighbor technique),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (contagionTechniqueBudget neighbor technique)).hRateLtOne
  · exact (budgetGeometricRate (contagionTechniqueBudget neighbor technique)).hInitialBoundPos

structure ContagionTechniqueKernelLiftBundle where
  source : ContagionSource
  neighbor : NeighborLoad
  technique : TechniqueWitness
  hCoupled : spilloverLoad source ≤ neighbor.phantomLoad
  budget : Nat
  hBudgetEq : budget = contagionTechniqueBudget neighbor technique
  driftGap : Nat
  hDriftGap : 0 < driftGap
deriving Repr

end TopologicalContagionTechniqueQueueKernelBridge

namespace ContagionTechniqueKernelLiftAdapter

abbrev ContagionTechniqueKernelLiftBundle :=
  TopologicalContagionTechniqueQueueKernelBridge.ContagionTechniqueKernelLiftBundle

theorem contagion_technique_continuous_ergodicity_lift
    (adapter : ContagionTechniqueKernelLiftBundle) :
    TopologicalContagionTechniqueQueueKernelBridge.spilloverLoad adapter.source ≤
      adapter.neighbor.phantomLoad ∧
    adapter.budget =
      TopologicalContagionTechniqueQueueKernelBridge.contagionTechniqueBudget
        adapter.neighbor
        adapter.technique ∧
    0 < adapter.driftGap :=
  ⟨adapter.hCoupled, adapter.hBudgetEq, adapter.hDriftGap⟩

end ContagionTechniqueKernelLiftAdapter
