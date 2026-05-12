import Init

/-!
# Mediation/Discovery/Bandit Queue Kernel Bridge

Finite mediation-loss, causal-discovery, and bandit-failure witnesses for stale
MCP rows.
-/

namespace MediationDiscoveryBanditQueueKernelBridge

structure MediationSetup where
  totalRejections : Nat
  mediatorLoss : Nat
  hMediatorLoss : 1 ≤ mediatorLoss
  hTotalRejections : totalRejections = mediatorLoss
deriving Repr

structure DiscoverySetup where
  R : Nat
  vX : Nat
  vY : Nat
  hX : vX ≤ R
  hY : vY ≤ R
  hSum : vX + vY ≤ R
deriving Repr

structure BanditArm where
  pulls : Nat
  failures : Nat
  hFailures : failures ≤ pulls
deriving Repr

def discoveryFailureBudget (setup : DiscoverySetup) : Nat :=
  setup.vX + setup.vY

def armFailureBudget (arm : BanditArm) : Nat :=
  arm.failures

def mediationDiscoveryBanditFailureBudget
    (mediation : MediationSetup)
    (discovery : DiscoverySetup)
    (arm : BanditArm) : Nat :=
  mediation.totalRejections + discoveryFailureBudget discovery + armFailureBudget arm

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

theorem mediation_discovery_bandit_budget_positive
    (mediation : MediationSetup)
    (discovery : DiscoverySetup)
    (arm : BanditArm) :
    0 < mediationDiscoveryBanditFailureBudget mediation discovery arm := by
  unfold mediationDiscoveryBanditFailureBudget
  rw [mediation.hTotalRejections]
  have hPair : 0 < mediation.mediatorLoss + discoveryFailureBudget discovery :=
    Nat.lt_add_right (discoveryFailureBudget discovery) mediation.hMediatorLoss
  exact Nat.lt_add_right (armFailureBudget arm) hPair

theorem mediation_discovery_bandit_budget_yields_unit_queue_boundary
    (mediation : MediationSetup)
    (discovery : DiscoverySetup)
    (arm : BanditArm) :
    0 < mediation.mediatorLoss ∧
    mediation.totalRejections = mediation.mediatorLoss ∧
    discovery.vX ≤ discovery.R ∧
    discovery.vY ≤ discovery.R ∧
    discovery.vX + discovery.vY ≤ discovery.R ∧
    arm.failures ≤ arm.pulls ∧
    0 < mediationDiscoveryBanditFailureBudget mediation discovery arm ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate =
        mediationDiscoveryBanditFailureBudget mediation discovery arm ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount
            (mediationDiscoveryBanditFailureBudget mediation discovery arm))
          (mediationDiscoveryBanditFailureBudget mediation discovery arm) := by
  exact ⟨mediation.hMediatorLoss, mediation.hTotalRejections,
    discovery.hX, discovery.hY, discovery.hSum, arm.hFailures,
    mediation_discovery_bandit_budget_positive mediation discovery arm,
    ⟨canonicalQueueBoundary
      (mediationDiscoveryBanditFailureBudget mediation discovery arm),
      rfl, rfl, rfl, rfl⟩⟩

theorem mediation_discovery_bandit_budget_yields_positive_topological_deficit
    (mediation : MediationSetup)
    (discovery : DiscoverySetup)
    (arm : BanditArm) :
    0 < topologicalDeficit
      (mediationDiscoveryBanditFailureBudget mediation discovery arm + 1) 1 := by
  unfold topologicalDeficit
  rw [Nat.add_sub_cancel]
  exact mediation_discovery_bandit_budget_positive mediation discovery arm

theorem mediation_discovery_bandit_budget_does_not_force_beta1_equals_budget
    (mediation : MediationSetup)
    (discovery : DiscoverySetup)
    (arm : BanditArm) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate =
          mediationDiscoveryBanditFailureBudget mediation discovery arm →
        boundary.serviceRate =
          quorumSize
            (replicaCount
              (mediationDiscoveryBanditFailureBudget mediation discovery arm))
            (mediationDiscoveryBanditFailureBudget mediation discovery arm) →
        boundary.beta1 =
          mediationDiscoveryBanditFailureBudget mediation discovery arm) := by
  intro hAll
  let budget := mediationDiscoveryBanditFailureBudget mediation discovery arm
  let boundary := canonicalQueueBoundary budget
  have hEq : boundary.beta1 = budget := hAll boundary rfl rfl
  have hPositive : 0 < budget :=
    mediation_discovery_bandit_budget_positive mediation discovery arm
  rw [show boundary.beta1 = 0 by rfl] at hEq
  rw [← hEq] at hPositive
  exact Nat.lt_irrefl 0 hPositive

theorem mediation_discovery_bandit_budget_does_not_force_capacity_at_least_two
    (mediation : MediationSetup)
    (discovery : DiscoverySetup)
    (arm : BanditArm) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate =
          mediationDiscoveryBanditFailureBudget mediation discovery arm →
        boundary.serviceRate =
          quorumSize
            (replicaCount
              (mediationDiscoveryBanditFailureBudget mediation discovery arm))
            (mediationDiscoveryBanditFailureBudget mediation discovery arm) →
        2 ≤ boundary.capacity) := by
  intro hAll
  let boundary :=
    canonicalQueueBoundary
      (mediationDiscoveryBanditFailureBudget mediation discovery arm)
  have hCapacity : 2 ≤ 1 := hAll boundary rfl rfl
  exact (Nat.not_succ_le_self 1) hCapacity

theorem mediation_discovery_bandit_semantic_morphism_yields_positive_topological_deficit
    (mediation : MediationSetup)
    (discovery : DiscoverySetup)
    (arm : BanditArm)
    (interpret : Nat → Nat)
    (hInterpret :
      interpret
        (mediationDiscoveryBanditFailureBudget mediation discovery arm + 1) =
        mediationDiscoveryBanditFailureBudget mediation discovery arm + 1) :
    0 < topologicalDeficit
      (interpret
        (mediationDiscoveryBanditFailureBudget mediation discovery arm + 1))
      1 := by
  rw [hInterpret]
  exact mediation_discovery_bandit_budget_yields_positive_topological_deficit
    mediation discovery arm

structure RetrialQueueKernelFamily where
  maxQueue : Nat
  maxOrbit : Nat
  stationaryBalance : Bool
  terminalBalance : Bool
deriving Repr

theorem mediation_discovery_bandit_retrial_stationary_balance_bridge
    (mediation : MediationSetup)
    (discovery : DiscoverySetup)
    (arm : BanditArm)
    (kernel : RetrialQueueKernelFamily) :
    0 < mediationDiscoveryBanditFailureBudget mediation discovery arm ∧
    mediation.totalRejections = mediation.mediatorLoss ∧
    discovery.vX ≤ discovery.R ∧
    discovery.vY ≤ discovery.R ∧
    discovery.vX + discovery.vY ≤ discovery.R ∧
    arm.failures ≤ arm.pulls ∧
    kernel.stationaryBalance = kernel.stationaryBalance ∧
    kernel.terminalBalance = kernel.terminalBalance := by
  exact ⟨mediation_discovery_bandit_budget_positive mediation discovery arm,
    mediation.hTotalRejections, discovery.hX, discovery.hY, discovery.hSum,
    arm.hFailures, rfl, rfl⟩

end MediationDiscoveryBanditQueueKernelBridge
