import Gnosis.Bridges.MediationQuorumQueueBridge

/-!
# Mediation Contrarian Boundaries

The quorum interpretation of mediation loss has the canonical one-path
boundary, so positive path width is not forced by the anchored rates.
-/

namespace MediationContrarianBoundaries

abbrev MediationSetup := MediationQuorumQueueBridge.MediationSetup
abbrev QueueBoundaryWitnessNat :=
  MediationQuorumQueueBridge.QueueBoundaryWitnessNat

def mediation_quorum_interpretation_yields_unit_boundary
    (m : MediationSetup) :
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = MediationQuorumQueueBridge.failureBudget m ∧
      boundary.serviceRate =
        MediationQuorumQueueBridge.quorumSize
          (MediationQuorumQueueBridge.replicaCount m)
          (MediationQuorumQueueBridge.failureBudget m) :=
  (MediationQuorumQueueBridge.mediation_loss_canonical_interpretation_yields_unit_queue_boundary m).2.2

theorem mediation_quorum_interpretation_does_not_force_positive_beta1
    (m : MediationSetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = MediationQuorumQueueBridge.failureBudget m →
        boundary.serviceRate =
          MediationQuorumQueueBridge.quorumSize
            (MediationQuorumQueueBridge.replicaCount m)
            (MediationQuorumQueueBridge.failureBudget m) →
        0 < boundary.beta1) := by
  intro hAll
  rcases mediation_quorum_interpretation_yields_unit_boundary m with
    ⟨boundary, hBetaZero, _hCapacity, hArrival, hService⟩
  have hPositive : 0 < boundary.beta1 := hAll boundary hArrival hService
  rw [hBetaZero] at hPositive
  exact Nat.lt_irrefl 0 hPositive

end MediationContrarianBoundaries
