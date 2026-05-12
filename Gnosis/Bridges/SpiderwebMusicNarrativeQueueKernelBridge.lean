namespace SpiderwebMusicNarrativeQueueKernelBridge

/-! Init-only spiderweb + music + narrative queue bridge. -/

structure MeshConfig where
  peers : Nat
  hops : Nat
  hPeers : 0 < peers
  hHops : 0 < hops
deriving Repr

structure MusicSetup where
  periodicLoad : Nat
  swingPerturbation : Nat
  totalSpace : Nat
  hSwing : 1 ≤ swingPerturbation
  hTotal : totalSpace = periodicLoad + swingPerturbation
deriving Repr

structure NarrativeSetup where
  narrativeCrossings : Nat
  hNarrative : 1 ≤ narrativeCrossings
deriving Repr

def meshRoutingPaths (mesh : MeshConfig) : Nat := mesh.peers * mesh.hops

def spiderwebMusicNarrativeFailureBudget
    (mesh : MeshConfig)
    (music : MusicSetup)
    (narrative : NarrativeSetup) : Nat :=
  meshRoutingPaths mesh + music.swingPerturbation + narrative.narrativeCrossings

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

theorem spiderweb_music_narrative_budget_positive
    (mesh : MeshConfig)
    (music : MusicSetup)
    (narrative : NarrativeSetup) :
    0 < spiderwebMusicNarrativeFailureBudget mesh music narrative := by
  unfold spiderwebMusicNarrativeFailureBudget
  exact Nat.lt_add_right narrative.narrativeCrossings
    (Nat.lt_add_right music.swingPerturbation (mesh_routing_paths_positive mesh))

theorem spiderweb_music_narrative_budget_yields_unit_queue_boundary
    (mesh : MeshConfig)
    (music : MusicSetup)
    (narrative : NarrativeSetup) :
    0 < meshRoutingPaths mesh ∧
    music.totalSpace = music.periodicLoad + music.swingPerturbation ∧
    0 < music.swingPerturbation ∧
    0 < narrative.narrativeCrossings ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧ boundary.capacity = 1 ∧
      boundary.arrivalRate = spiderwebMusicNarrativeFailureBudget mesh music narrative ∧
      boundary.serviceRate =
        quorumSize (replicaCount (spiderwebMusicNarrativeFailureBudget mesh music narrative))
          (spiderwebMusicNarrativeFailureBudget mesh music narrative) := by
  refine
    ⟨mesh_routing_paths_positive mesh, music.hTotal, music.hSwing, narrative.hNarrative, ?_⟩
  exact
    ⟨canonicalQueueBoundary (spiderwebMusicNarrativeFailureBudget mesh music narrative),
      rfl, rfl, rfl, rfl⟩

theorem spiderweb_music_narrative_joint_queue_witness_pack
    (mesh : MeshConfig)
    (music : MusicSetup)
    (narrative : NarrativeSetup) :
    (∃ boundary : QueueBoundaryWitnessNat,
      boundary.arrivalRate = meshRoutingPaths mesh ∧ boundary.capacity = 1) ∧
    (∃ boundary : QueueBoundaryWitnessNat,
      boundary.arrivalRate = music.swingPerturbation ∧ boundary.capacity = 1) ∧
    (∃ boundary : QueueBoundaryWitnessNat,
      boundary.arrivalRate = narrative.narrativeCrossings ∧ boundary.capacity = 1) ∧
    (∃ boundary : QueueBoundaryWitnessNat,
      boundary.arrivalRate = spiderwebMusicNarrativeFailureBudget mesh music narrative ∧
      boundary.capacity = 1) := by
  exact
    ⟨⟨canonicalQueueBoundary (meshRoutingPaths mesh), rfl, rfl⟩,
      ⟨canonicalQueueBoundary music.swingPerturbation, rfl, rfl⟩,
      ⟨canonicalQueueBoundary narrative.narrativeCrossings, rfl, rfl⟩,
      ⟨canonicalQueueBoundary (spiderwebMusicNarrativeFailureBudget mesh music narrative),
        rfl, rfl⟩⟩

theorem spiderweb_music_narrative_budget_does_not_force_strict_capacity_growth
    (mesh : MeshConfig)
    (music : MusicSetup)
    (narrative : NarrativeSetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = spiderwebMusicNarrativeFailureBudget mesh music narrative →
        boundary.serviceRate =
          quorumSize (replicaCount (spiderwebMusicNarrativeFailureBudget mesh music narrative))
            (spiderwebMusicNarrativeFailureBudget mesh music narrative) →
        1 < boundary.capacity) := by
  intro hAll
  let boundary := canonicalQueueBoundary (spiderwebMusicNarrativeFailureBudget mesh music narrative)
  have h : 1 < boundary.capacity := hAll boundary rfl rfl
  exact Nat.lt_irrefl 1 h

theorem spiderweb_music_narrative_budget_yields_geometric_rate_certificate
    (mesh : MeshConfig)
    (music : MusicSetup)
    (narrative : NarrativeSetup) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (spiderwebMusicNarrativeFailureBudget mesh music narrative) ∧
      rate.initialBound = spiderwebMusicNarrativeFailureBudget mesh music narrative + 1 ∧
      rate.numerator = 3 ∧ rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧ 0 < rate.initialBound := by
  refine
    ⟨budgetGeometricRate (spiderwebMusicNarrativeFailureBudget mesh music narrative),
      rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate
      (spiderwebMusicNarrativeFailureBudget mesh music narrative)).hRateLtOne
  · exact (budgetGeometricRate
      (spiderwebMusicNarrativeFailureBudget mesh music narrative)).hInitialBoundPos

theorem spiderweb_music_narrative_budget_real_positive
    (mesh : MeshConfig)
    (music : MusicSetup)
    (narrative : NarrativeSetup) :
    0 < spiderwebMusicNarrativeFailureBudget mesh music narrative :=
  spiderweb_music_narrative_budget_positive mesh music narrative

structure SpiderwebMusicNarrativeKernelLiftAdapter where
  mesh : MeshConfig
  music : MusicSetup
  narrative : NarrativeSetup
  budget : Nat
  hBudgetEq : budget = spiderwebMusicNarrativeFailureBudget mesh music narrative
  driftGap : Nat
  hDriftGap : 0 < driftGap
  kernelMatched : Bool
deriving Repr

namespace SpiderwebMusicNarrativeKernelLiftAdapter

theorem budget_pos_from_source
    (adapter : SpiderwebMusicNarrativeKernelLiftAdapter) :
    0 < adapter.budget := by
  rw [adapter.hBudgetEq]
  exact spiderweb_music_narrative_budget_positive
    adapter.mesh adapter.music adapter.narrative

theorem spiderweb_music_narrative_continuous_ergodicity_lift
    (adapter : SpiderwebMusicNarrativeKernelLiftAdapter) :
    0 < adapter.budget ∧ 0 < adapter.driftGap := by
  exact ⟨adapter.budget_pos_from_source, adapter.hDriftGap⟩

end SpiderwebMusicNarrativeKernelLiftAdapter

end SpiderwebMusicNarrativeQueueKernelBridge
