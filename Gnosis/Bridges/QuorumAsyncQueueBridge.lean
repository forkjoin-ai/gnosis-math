import Gnosis.QuorumAsyncNetwork

/-!
# Quorum Async Queue Bridge

Connected-quorum exactness routed through a strict-majority queue boundary,
positive transport deficit, and small kernel-lift certificate records.
-/

namespace QuorumAsyncQueueBridge

def replicaCountFromBudget (failureBudget : Nat) : Nat :=
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
    serviceRate := quorumSize (replicaCountFromBudget failureBudget) failureBudget }

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

def connectedCardinalityGeometricRate (connected : List Nat) : GeometricRateNat :=
  { numerator := 3
    denominator := 4
    initialBound := connected.length + 1
    hRateLtOne := by decide
    hDenomPos := by decide
    hInitialBoundPos := Nat.succ_pos connected.length }

theorem connected_quorum_exactness_and_majority_yields_unit_boundary
    {quorum connected : List Nat}
    {storedVersion : Nat → Nat}
    {ackedBallot : Nat}
    (hAckMember : ∃ replica ∈ quorum, ackedBallot ≤ storedVersion replica)
    (hNoReplicaAhead : ∀ replica ∈ quorum, storedVersion replica ≤ ackedBallot)
    (_hMajority : 2 * ackedBallot < connected.length + 1) :
    Gnosis.readValue quorum storedVersion = ackedBallot ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = ackedBallot ∧
      boundary.serviceRate =
        quorumSize (replicaCountFromBudget ackedBallot) ackedBallot := by
  exact
    ⟨Gnosis.connected_quorum_read_exact_of_coverage hAckMember hNoReplicaAhead,
      ⟨canonicalQueueBoundary ackedBallot, rfl, rfl, rfl, rfl⟩⟩

theorem connected_quorum_exactness_and_majority_does_not_force_positive_beta1
    {quorum connected : List Nat}
    {storedVersion : Nat → Nat}
    {ackedBallot : Nat}
    (_hAckMember : ∃ replica ∈ quorum, ackedBallot ≤ storedVersion replica)
    (_hNoReplicaAhead : ∀ replica ∈ quorum, storedVersion replica ≤ ackedBallot)
    (_hMajority : 2 * ackedBallot < connected.length + 1) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = ackedBallot →
        boundary.serviceRate =
          quorumSize (replicaCountFromBudget ackedBallot) ackedBallot →
        0 < boundary.beta1) := by
  intro hAll
  let boundary := canonicalQueueBoundary ackedBallot
  have hPositive : 0 < boundary.beta1 :=
    hAll boundary rfl rfl
  exact Nat.lt_irrefl 0 hPositive

theorem connected_quorum_exactness_and_positive_budget_yields_positive_topological_deficit
    {quorum connected : List Nat}
    {storedVersion : Nat → Nat}
    {ackedBallot : Nat}
    (hAckMember : ∃ replica ∈ quorum, ackedBallot ≤ storedVersion replica)
    (hNoReplicaAhead : ∀ replica ∈ quorum, storedVersion replica ≤ ackedBallot)
    (_hMajority : 2 * ackedBallot < connected.length + 1)
    (hPositiveBudget : 0 < ackedBallot) :
    Gnosis.readValue quorum storedVersion = ackedBallot ∧
    0 < topologicalDeficit (ackedBallot + 1) 1 := by
  refine
    ⟨Gnosis.connected_quorum_read_exact_of_coverage hAckMember hNoReplicaAhead, ?_⟩
  unfold topologicalDeficit
  rw [Nat.add_sub_cancel]
  exact hPositiveBudget

theorem connected_quorum_semantic_morphism_yields_positive_topological_deficit
    {quorum connected : List Nat}
    {storedVersion : Nat → Nat}
    {ackedBallot : Nat}
    (hAckMember : ∃ replica ∈ quorum, ackedBallot ≤ storedVersion replica)
    (hNoReplicaAhead : ∀ replica ∈ quorum, storedVersion replica ≤ ackedBallot)
    (hMajority : 2 * ackedBallot < connected.length + 1)
    (hPositiveBudget : 0 < ackedBallot)
    (interpret : Nat → Nat)
    (hMorphism : interpret (ackedBallot + 1) = ackedBallot + 1) :
    Gnosis.readValue quorum storedVersion = ackedBallot ∧
    0 < topologicalDeficit (interpret (ackedBallot + 1)) 1 := by
  refine
    ⟨Gnosis.connected_quorum_read_exact_of_coverage hAckMember hNoReplicaAhead, ?_⟩
  rw [hMorphism]
  exact
    (connected_quorum_exactness_and_positive_budget_yields_positive_topological_deficit
        hAckMember hNoReplicaAhead hMajority hPositiveBudget).2

theorem connected_quorum_exactness_and_positive_budget_does_not_force_universal_nonpositive_deficit
    {quorum connected : List Nat}
    {storedVersion : Nat → Nat}
    {ackedBallot : Nat}
    (hAckMember : ∃ replica ∈ quorum, ackedBallot ≤ storedVersion replica)
    (hNoReplicaAhead : ∀ replica ∈ quorum, storedVersion replica ≤ ackedBallot)
    (hMajority : 2 * ackedBallot < connected.length + 1)
    (hPositiveBudget : 0 < ackedBallot) :
    ¬ (∀ transportStreams : Nat,
        topologicalDeficit (ackedBallot + 1) transportStreams ≤ 0) := by
  intro hUniversal
  have hPositive :
      0 < topologicalDeficit (ackedBallot + 1) 1 :=
    (connected_quorum_exactness_and_positive_budget_yields_positive_topological_deficit
      hAckMember hNoReplicaAhead hMajority hPositiveBudget).2
  exact Nat.not_lt_of_ge (hUniversal 1) hPositive

theorem connected_quorum_exactness_majority_and_positive_budget_yield_boundary_and_positive_deficit
    {quorum connected : List Nat}
    {storedVersion : Nat → Nat}
    {ackedBallot : Nat}
    (hAckMember : ∃ replica ∈ quorum, ackedBallot ≤ storedVersion replica)
    (hNoReplicaAhead : ∀ replica ∈ quorum, storedVersion replica ≤ ackedBallot)
    (hMajority : 2 * ackedBallot < connected.length + 1)
    (hPositiveBudget : 0 < ackedBallot) :
    Gnosis.readValue quorum storedVersion = ackedBallot ∧
    (∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = ackedBallot ∧
      boundary.serviceRate =
        quorumSize (replicaCountFromBudget ackedBallot) ackedBallot) ∧
    0 < topologicalDeficit (ackedBallot + 1) 1 := by
  have hBoundary :=
    connected_quorum_exactness_and_majority_yields_unit_boundary
      hAckMember hNoReplicaAhead hMajority
  have hDeficit :=
    connected_quorum_exactness_and_positive_budget_yields_positive_topological_deficit
      hAckMember hNoReplicaAhead hMajority hPositiveBudget
  exact ⟨hBoundary.1, hBoundary.2, hDeficit.2⟩

theorem nonempty_connected_quorum_yields_geometric_rate_certificate
    (connected : List Nat)
    (hNonempty : connected ≠ []) :
    ∃ rate : GeometricRateNat,
      rate = connectedCardinalityGeometricRate connected ∧
      rate.initialBound = connected.length + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      1 < rate.initialBound := by
  refine
    ⟨connectedCardinalityGeometricRate connected, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (connectedCardinalityGeometricRate connected).hRateLtOne
  · cases connected with
    | nil => exact False.elim (hNonempty rfl)
    | cons _ tail =>
        exact Nat.succ_lt_succ (Nat.succ_pos tail.length)

structure ConnectedQuorumKernelLiftBundle where
  quorum : List Nat
  connected : List Nat
  storedVersion : Nat → Nat
  ackedBallot : Nat
  hAckMember : ∃ replica ∈ quorum, ackedBallot ≤ storedVersion replica
  hNoReplicaAhead : ∀ replica ∈ quorum, storedVersion replica ≤ ackedBallot
  hMajority : 2 * ackedBallot < connected.length + 1
  hPositiveBudget : 0 < ackedBallot
  discreteDriftGap : Nat
  continuousDriftGap : Nat
  hDiscreteDriftGap : 0 < discreteDriftGap
  hContinuousDriftGap : 0 < continuousDriftGap

end QuorumAsyncQueueBridge

namespace ConnectedQuorumKernelLiftAdapter

abbrev ConnectedQuorumKernelLiftBundle :=
  QuorumAsyncQueueBridge.ConnectedQuorumKernelLiftBundle

theorem connected_quorum_continuous_ergodicity_and_deficit_lift
    (adapter : ConnectedQuorumKernelLiftBundle) :
    Gnosis.readValue adapter.quorum adapter.storedVersion = adapter.ackedBallot ∧
    0 < QuorumAsyncQueueBridge.topologicalDeficit (adapter.ackedBallot + 1) 1 ∧
    0 < adapter.discreteDriftGap ∧
    0 < adapter.continuousDriftGap := by
  exact
    ⟨Gnosis.connected_quorum_read_exact_of_coverage
        adapter.hAckMember
        adapter.hNoReplicaAhead,
      (QuorumAsyncQueueBridge.connected_quorum_exactness_and_positive_budget_yields_positive_topological_deficit
        adapter.hAckMember
        adapter.hNoReplicaAhead
        adapter.hMajority
        adapter.hPositiveBudget).2,
      adapter.hDiscreteDriftGap,
      adapter.hContinuousDriftGap⟩

end ConnectedQuorumKernelLiftAdapter
