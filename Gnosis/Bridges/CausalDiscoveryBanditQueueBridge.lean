namespace CausalDiscoveryBanditQueueBridge

/-!
Init-only salvage of the causal-discovery/bandit queue bridge.

The legacy module had useful finite queue-budget content but depended on
Mathlib automation. This replacement keeps the discovery decomposition, bandit
failure budget, queue witnesses, positive deficit, geometric rate, and
kernel-lift certificates as Nat-level data.
-/

structure DiscoverySetup where
  R : Nat
  vX : Nat
  vY : Nat
  hX : vX ≤ R
  hY : vY ≤ R
  hSum : vX + vY ≤ R
deriving Repr

structure BanditArm where
  failures : Nat
deriving DecidableEq, Repr

def discoveryFailureBudget (setup : DiscoverySetup) : Nat :=
  setup.vX + setup.vY

def armFailureBudget (arm : BanditArm) : Nat :=
  arm.failures

def replicaCount (failureBudget : Nat) : Nat :=
  2 * failureBudget + 1

def quorumSize (_replicas failureBudget : Nat) : Nat :=
  failureBudget + 1

structure QueueBoundaryWitnessNat where
  beta1 : Nat
  capacity : Nat
  arrivalRate : Nat
  serviceRate : Nat
deriving DecidableEq, Repr

def canonicalQueueBoundary (failureBudget : Nat) : QueueBoundaryWitnessNat :=
  { beta1 := 0
    capacity := 1
    arrivalRate := failureBudget
    serviceRate := quorumSize (replicaCount failureBudget) failureBudget }

def topologicalDeficit (pathCount channelCount : Nat) : Nat :=
  pathCount - channelCount

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

theorem causal_discovery_independence_yields_unit_queue_boundary
    (setup : DiscoverySetup) :
    discoveryFailureBudget setup = setup.vX + setup.vY ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = discoveryFailureBudget setup ∧
      boundary.serviceRate =
        quorumSize (replicaCount (discoveryFailureBudget setup))
          (discoveryFailureBudget setup) := by
  refine ⟨rfl, ?_⟩
  exact ⟨canonicalQueueBoundary (discoveryFailureBudget setup), rfl, rfl, rfl, rfl⟩

theorem causal_discovery_independence_does_not_force_positive_beta1
    (setup : DiscoverySetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = discoveryFailureBudget setup →
        boundary.serviceRate =
          quorumSize (replicaCount (discoveryFailureBudget setup))
            (discoveryFailureBudget setup) →
        0 < boundary.beta1) := by
  intro hAll
  let boundary := canonicalQueueBoundary (discoveryFailureBudget setup)
  have h : 0 < boundary.beta1 := hAll boundary rfl rfl
  exact Nat.lt_irrefl 0 h

theorem bandit_arm_failures_yield_unit_queue_boundary
    (arm : BanditArm) :
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = armFailureBudget arm ∧
      boundary.serviceRate =
        quorumSize (replicaCount (armFailureBudget arm)) (armFailureBudget arm) := by
  exact ⟨canonicalQueueBoundary (armFailureBudget arm), rfl, rfl, rfl, rfl⟩

theorem causal_discovery_bandit_budget_yields_unit_queue_boundary
    (setup : DiscoverySetup)
    (arm : BanditArm)
    (hBridge : armFailureBudget arm = discoveryFailureBudget setup) :
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = discoveryFailureBudget setup ∧
      boundary.serviceRate =
        quorumSize (replicaCount (discoveryFailureBudget setup))
          (discoveryFailureBudget setup) := by
  rcases bandit_arm_failures_yield_unit_queue_boundary arm with
    ⟨boundary, hBeta, hCapacity, hArrival, hService⟩
  refine ⟨boundary, hBeta, hCapacity, ?_, ?_⟩
  · rw [← hBridge]
    exact hArrival
  · rw [← hBridge]
    exact hService

theorem causal_bandit_positive_budget_yields_positive_topological_deficit
    (setup : DiscoverySetup)
    (arm : BanditArm)
    (hBridge : armFailureBudget arm = discoveryFailureBudget setup)
    (hPositive : 0 < armFailureBudget arm) :
    0 < topologicalDeficit (discoveryFailureBudget setup + 1) 1 := by
  unfold topologicalDeficit
  rw [← hBridge]
  rw [Nat.add_sub_cancel]
  exact hPositive

theorem bandit_arm_failures_do_not_force_positive_beta1
    (arm : BanditArm) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = armFailureBudget arm →
        boundary.serviceRate =
          quorumSize (replicaCount (armFailureBudget arm)) (armFailureBudget arm) →
        0 < boundary.beta1) := by
  intro hAll
  let boundary := canonicalQueueBoundary (armFailureBudget arm)
  have h : 0 < boundary.beta1 := hAll boundary rfl rfl
  exact Nat.lt_irrefl 0 h

theorem causal_discovery_bandit_budget_does_not_force_beta1_equals_budget
    (setup : DiscoverySetup)
    (arm : BanditArm)
    (hBridge : armFailureBudget arm = discoveryFailureBudget setup)
    (hPositive : 0 < armFailureBudget arm) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = discoveryFailureBudget setup →
        boundary.serviceRate =
          quorumSize (replicaCount (discoveryFailureBudget setup))
            (discoveryFailureBudget setup) →
        boundary.beta1 = discoveryFailureBudget setup) := by
  intro hAll
  let boundary := canonicalQueueBoundary (discoveryFailureBudget setup)
  have hEq : boundary.beta1 = discoveryFailureBudget setup := hAll boundary rfl rfl
  have hBudget : 0 < discoveryFailureBudget setup := by
    rw [← hBridge]
    exact hPositive
  rw [show boundary.beta1 = 0 by rfl] at hEq
  rw [← hEq] at hBudget
  exact Nat.lt_irrefl 0 hBudget

theorem bandit_arm_failures_yield_geometric_rate_certificate
    (arm : BanditArm) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (armFailureBudget arm) ∧
      rate.initialBound = armFailureBudget arm + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨budgetGeometricRate (armFailureBudget arm), rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (armFailureBudget arm)).hRateLtOne
  · exact (budgetGeometricRate (armFailureBudget arm)).hInitialBoundPos

structure CausalBanditKernelLiftAdapter where
  setup : DiscoverySetup
  arm : BanditArm
  hBridge : armFailureBudget arm = discoveryFailureBudget setup
  budget : Nat
  hBudgetEq : budget = armFailureBudget arm
  hBudgetPos : 0 < budget
  driftGap : Nat
  hDriftGap : 0 < driftGap
  kernelMatched : Bool
deriving Repr

namespace CausalBanditKernelLiftAdapter

theorem causal_bandit_continuous_ergodicity_lift
    (adapter : CausalBanditKernelLiftAdapter) :
    adapter.budget = armFailureBudget adapter.arm ∧
    0 < adapter.budget ∧
    0 < adapter.driftGap :=
  ⟨adapter.hBudgetEq, adapter.hBudgetPos, adapter.hDriftGap⟩

end CausalBanditKernelLiftAdapter

theorem causal_bandit_interpretation_certificate_lift
    (setup : DiscoverySetup)
    (arm : BanditArm)
    (hBridge : armFailureBudget arm = discoveryFailureBudget setup)
    (budget : Nat)
    (hBudgetEq : budget = armFailureBudget arm)
    (hBudgetPos : 0 < budget)
    (driftGap : Nat)
    (hDriftGap : 0 < driftGap) :
    budget = discoveryFailureBudget setup ∧
    0 < budget ∧
    0 < driftGap := by
  refine ⟨?_, hBudgetPos, hDriftGap⟩
  rw [hBudgetEq, hBridge]

end CausalDiscoveryBanditQueueBridge
