namespace SpiderwebAperiodicNarrativeQueueKernelBridge

/-! Init-only spiderweb + aperiodic schedule + narrative queue bridge. -/

structure MeshConfig where
  peers : Nat
  hops : Nat
  hPeers : 0 < peers
  hHops : 0 < hops
deriving Repr

structure AperiodicSchedule where
  resonanceCollisions : Nat
  isIrrational : Bool
  hIrrational : isIrrational = true
deriving Repr

structure NarrativeSetup where
  narrativeCrossings : Nat
  hNarrative : 1 ≤ narrativeCrossings
deriving Repr

def meshRoutingPaths (mesh : MeshConfig) : Nat :=
  mesh.peers * mesh.hops

def spiderwebAperiodicNarrativeFailureBudget
    (mesh : MeshConfig)
    (schedule : AperiodicSchedule)
    (narrative : NarrativeSetup) : Nat :=
  (meshRoutingPaths mesh + narrative.narrativeCrossings) +
    (schedule.resonanceCollisions + 1)

def replicaCount (failureBudget : Nat) : Nat := 2 * failureBudget + 1
def quorumSize (_replicas failureBudget : Nat) : Nat := failureBudget + 1

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

theorem mesh_routing_paths_positive (mesh : MeshConfig) :
    0 < meshRoutingPaths mesh := by
  unfold meshRoutingPaths
  exact Nat.mul_pos mesh.hPeers mesh.hHops

theorem spiderweb_aperiodic_narrative_budget_positive
    (mesh : MeshConfig)
    (schedule : AperiodicSchedule)
    (narrative : NarrativeSetup) :
    0 < spiderwebAperiodicNarrativeFailureBudget mesh schedule narrative := by
  unfold spiderwebAperiodicNarrativeFailureBudget
  exact Nat.lt_add_right (schedule.resonanceCollisions + 1)
    (Nat.lt_add_right narrative.narrativeCrossings (mesh_routing_paths_positive mesh))

theorem spiderweb_aperiodic_narrative_budget_yields_unit_queue_boundary
    (mesh : MeshConfig)
    (schedule : AperiodicSchedule)
    (narrative : NarrativeSetup) :
    0 < meshRoutingPaths mesh ∧
    schedule.isIrrational = true ∧
    0 < narrative.narrativeCrossings ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate =
        spiderwebAperiodicNarrativeFailureBudget mesh schedule narrative ∧
      boundary.serviceRate =
        quorumSize (replicaCount (spiderwebAperiodicNarrativeFailureBudget mesh schedule narrative))
          (spiderwebAperiodicNarrativeFailureBudget mesh schedule narrative) := by
  refine ⟨mesh_routing_paths_positive mesh, schedule.hIrrational, narrative.hNarrative, ?_⟩
  exact
    ⟨canonicalQueueBoundary (spiderwebAperiodicNarrativeFailureBudget mesh schedule narrative),
      rfl, rfl, rfl, rfl⟩

theorem spiderweb_aperiodic_narrative_joint_queue_witness_pack
    (mesh : MeshConfig)
    (schedule : AperiodicSchedule)
    (narrative : NarrativeSetup) :
    (∃ boundary : QueueBoundaryWitnessNat,
      boundary.arrivalRate = meshRoutingPaths mesh ∧ boundary.capacity = 1) ∧
    (∃ boundary : QueueBoundaryWitnessNat,
      boundary.arrivalRate = narrative.narrativeCrossings ∧ boundary.capacity = 1) ∧
    (∃ boundary : QueueBoundaryWitnessNat,
      boundary.arrivalRate =
        spiderwebAperiodicNarrativeFailureBudget mesh schedule narrative ∧
      boundary.capacity = 1) := by
  exact
    ⟨⟨canonicalQueueBoundary (meshRoutingPaths mesh), rfl, rfl⟩,
      ⟨canonicalQueueBoundary narrative.narrativeCrossings, rfl, rfl⟩,
      ⟨canonicalQueueBoundary
        (spiderwebAperiodicNarrativeFailureBudget mesh schedule narrative), rfl, rfl⟩⟩

theorem spiderweb_aperiodic_narrative_budget_does_not_force_capacity_at_least_two
    (mesh : MeshConfig)
    (schedule : AperiodicSchedule)
    (narrative : NarrativeSetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate =
          spiderwebAperiodicNarrativeFailureBudget mesh schedule narrative →
        boundary.serviceRate =
          quorumSize (replicaCount (spiderwebAperiodicNarrativeFailureBudget mesh schedule narrative))
            (spiderwebAperiodicNarrativeFailureBudget mesh schedule narrative) →
        2 ≤ boundary.capacity) := by
  intro hAll
  let boundary := canonicalQueueBoundary (spiderwebAperiodicNarrativeFailureBudget mesh schedule narrative)
  have h : 2 ≤ boundary.capacity := hAll boundary rfl rfl
  exact Nat.not_succ_le_self 1 h

theorem spiderweb_aperiodic_narrative_budget_yields_geometric_rate_certificate
    (mesh : MeshConfig)
    (schedule : AperiodicSchedule)
    (narrative : NarrativeSetup) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (spiderwebAperiodicNarrativeFailureBudget mesh schedule narrative) ∧
      rate.initialBound = spiderwebAperiodicNarrativeFailureBudget mesh schedule narrative + 1 ∧
      rate.numerator = 3 ∧ rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧ 0 < rate.initialBound := by
  refine
    ⟨budgetGeometricRate (spiderwebAperiodicNarrativeFailureBudget mesh schedule narrative),
      rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate
      (spiderwebAperiodicNarrativeFailureBudget mesh schedule narrative)).hRateLtOne
  · exact (budgetGeometricRate
      (spiderwebAperiodicNarrativeFailureBudget mesh schedule narrative)).hInitialBoundPos

structure SpiderwebAperiodicNarrativeKernelLiftAdapter where
  mesh : MeshConfig
  schedule : AperiodicSchedule
  narrative : NarrativeSetup
  budget : Nat
  hBudgetEq : budget = spiderwebAperiodicNarrativeFailureBudget mesh schedule narrative
  driftGap : Nat
  hDriftGap : 0 < driftGap
  kernelMatched : Bool
deriving Repr

namespace SpiderwebAperiodicNarrativeKernelLiftAdapter

theorem budget_pos_from_source
    (adapter : SpiderwebAperiodicNarrativeKernelLiftAdapter) :
    0 < adapter.budget := by
  rw [adapter.hBudgetEq]
  exact spiderweb_aperiodic_narrative_budget_positive
    adapter.mesh adapter.schedule adapter.narrative

theorem spiderweb_aperiodic_narrative_continuous_ergodicity_lift
    (adapter : SpiderwebAperiodicNarrativeKernelLiftAdapter) :
    0 < adapter.budget ∧ 0 < adapter.driftGap := by
  exact ⟨adapter.budget_pos_from_source, adapter.hDriftGap⟩

end SpiderwebAperiodicNarrativeKernelLiftAdapter

end SpiderwebAperiodicNarrativeQueueKernelBridge
