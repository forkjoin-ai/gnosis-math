import Init

/-!
# Stress/Aesthetics Queue Kernel Bridge

Finite stress-energy plus UI-friction budget witnesses for the stale MCP bridge.
-/

namespace StressAestheticsQueueKernelBridge

structure StressEnergyWitness where
  stressEnergy : Nat
  n : Nat
  hPositiveN : 0 < n
deriving Repr

structure AestheticsFrictionWitness where
  chaoticFriction : Nat
  orderedFriction : Nat
  precomputationCost : Nat
  hMinimized : orderedFriction + precomputationCost < chaoticFriction
deriving Repr

def aestheticsFrictionGain (ui : AestheticsFrictionWitness) : Nat :=
  ui.chaoticFriction - ui.orderedFriction

def stressAestheticsBudget
    (stress : StressEnergyWitness)
    (ui : AestheticsFrictionWitness) : Nat :=
  stress.stressEnergy + aestheticsFrictionGain ui

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

theorem stress_aesthetics_budget_yields_unit_queue_boundary
    (stress : StressEnergyWitness)
    (ui : AestheticsFrictionWitness) :
    0 < stress.n ∧
    ui.orderedFriction + ui.precomputationCost < ui.chaoticFriction ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = stressAestheticsBudget stress ui ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (stressAestheticsBudget stress ui))
          (stressAestheticsBudget stress ui) := by
  exact ⟨stress.hPositiveN, ui.hMinimized,
    ⟨canonicalQueueBoundary (stressAestheticsBudget stress ui),
      rfl, rfl, rfl, rfl⟩⟩

theorem stress_aesthetics_budget_does_not_force_beta1_equals_budget
    (stress : StressEnergyWitness)
    (ui : AestheticsFrictionWitness)
    (hPositive : 0 < stressAestheticsBudget stress ui) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = stressAestheticsBudget stress ui →
        boundary.serviceRate =
          quorumSize
            (replicaCount (stressAestheticsBudget stress ui))
            (stressAestheticsBudget stress ui) →
        boundary.beta1 = stressAestheticsBudget stress ui) := by
  intro hAll
  let boundary := canonicalQueueBoundary (stressAestheticsBudget stress ui)
  have hEq : boundary.beta1 = stressAestheticsBudget stress ui :=
    hAll boundary rfl rfl
  rw [show boundary.beta1 = 0 by rfl] at hEq
  rw [← hEq] at hPositive
  exact Nat.lt_irrefl 0 hPositive

theorem stress_aesthetics_budget_yields_geometric_rate_certificate
    (stress : StressEnergyWitness)
    (ui : AestheticsFrictionWitness) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (stressAestheticsBudget stress ui) ∧
      rate.initialBound = stressAestheticsBudget stress ui + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨budgetGeometricRate (stressAestheticsBudget stress ui),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (stressAestheticsBudget stress ui)).hRateLtOne
  · exact (budgetGeometricRate (stressAestheticsBudget stress ui)).hInitialBoundPos

structure StressAestheticsKernelLiftBundle where
  stress : StressEnergyWitness
  ui : AestheticsFrictionWitness
  budget : Nat
  hBudgetEq : budget = stressAestheticsBudget stress ui
  driftGap : Nat
  hDriftGap : 0 < driftGap
deriving Repr

end StressAestheticsQueueKernelBridge

namespace StressAestheticsKernelLiftAdapter

abbrev StressAestheticsKernelLiftBundle :=
  StressAestheticsQueueKernelBridge.StressAestheticsKernelLiftBundle

theorem stress_aesthetics_continuous_ergodicity_lift
    (adapter : StressAestheticsKernelLiftBundle) :
    adapter.budget =
      StressAestheticsQueueKernelBridge.stressAestheticsBudget
        adapter.stress
        adapter.ui ∧
    adapter.ui.orderedFriction + adapter.ui.precomputationCost <
      adapter.ui.chaoticFriction ∧
    0 < adapter.driftGap :=
  ⟨adapter.hBudgetEq, adapter.ui.hMinimized, adapter.hDriftGap⟩

end StressAestheticsKernelLiftAdapter
