import Gnosis.Bridges.MediationQueueBoundaryBridge

/-!
# Mediation Quorum Queue Bridge

Positive mediation loss interpreted as a strict-majority quorum budget and
routed to a canonical one-path queue boundary.
-/

namespace MediationQuorumQueueBridge

abbrev MediationSetup := Gnosis.CausalMediation.MediationSetup

def failureBudget (m : MediationSetup) : Nat :=
  m.mediatorLoss

def replicaCount (m : MediationSetup) : Nat :=
  2 * failureBudget m + 1

def quorumSize (_replicas failureBudget : Nat) : Nat :=
  failureBudget + 1

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
    serviceRate := quorumSize (2 * budget + 1) budget }

theorem mediation_loss_quorum_interpretation_is_strict_majority
    (m : MediationSetup) :
    2 * failureBudget m < replicaCount m := by
  unfold replicaCount
  exact Nat.lt_succ_self (2 * failureBudget m)

theorem mediation_loss_canonical_interpretation_yields_unit_queue_boundary
    (m : MediationSetup) :
    1 ≤ failureBudget m ∧
    2 * failureBudget m < replicaCount m ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = failureBudget m ∧
      boundary.serviceRate = quorumSize (replicaCount m) (failureBudget m) := by
  refine
    ⟨m.mediatorLossPositive,
      mediation_loss_quorum_interpretation_is_strict_majority m,
      ?_⟩
  exact ⟨canonicalQueueBoundary (failureBudget m), rfl, rfl, rfl, rfl⟩

end MediationQuorumQueueBridge
