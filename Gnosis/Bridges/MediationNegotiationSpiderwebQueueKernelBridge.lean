import Init

/-!
# Mediation/Negotiation/Spiderweb Queue Kernel Bridge

Init-only finite witnesses for the mediation-loss, BATNA trauma-gap, and
spiderweb routing-path MCP rows.
-/

namespace MediationNegotiationSpiderwebQueueKernelBridge

structure MediationSetup where
  mediatorLoss : Nat
  hMediatorLoss : 1 ≤ mediatorLoss
deriving Repr

structure NegotiationSetup where
  untanglingWattsCost : Nat
  slamTraumaPenalty : Nat
  hPenalty : untanglingWattsCost + 1 ≤ slamTraumaPenalty
deriving Repr

structure MeshConfig where
  peers : Nat
  hops : Nat
  hPeers : 0 < peers
  hHops : 0 < hops
deriving Repr

def batnaTraumaGap (negotiation : NegotiationSetup) : Nat :=
  negotiation.slamTraumaPenalty - negotiation.untanglingWattsCost

def meshRoutingPaths (mesh : MeshConfig) : Nat := mesh.peers * mesh.hops

def mediationNegotiationSpiderwebFailureBudget
    (mediation : MediationSetup) (negotiation : NegotiationSetup) (mesh : MeshConfig) :
    Nat :=
  mediation.mediatorLoss + batnaTraumaGap negotiation + meshRoutingPaths mesh

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

theorem batna_trauma_gap_positive (negotiation : NegotiationSetup) :
    0 < batnaTraumaGap negotiation := by
  unfold batnaTraumaGap
  exact Nat.sub_pos_of_lt negotiation.hPenalty

theorem mesh_routing_paths_positive (mesh : MeshConfig) :
    0 < meshRoutingPaths mesh := by
  unfold meshRoutingPaths
  exact Nat.mul_pos mesh.hPeers mesh.hHops

theorem mediation_negotiation_spiderweb_budget_positive
    (mediation : MediationSetup) (negotiation : NegotiationSetup) (mesh : MeshConfig) :
    0 < mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh := by
  unfold mediationNegotiationSpiderwebFailureBudget
  exact Nat.lt_add_right (meshRoutingPaths mesh)
    (Nat.lt_add_right (batnaTraumaGap negotiation) mediation.hMediatorLoss)

theorem mediation_negotiation_spiderweb_budget_yields_unit_queue_boundary
    (mediation : MediationSetup) (negotiation : NegotiationSetup) (mesh : MeshConfig) :
    0 < mediation.mediatorLoss ∧
    0 < batnaTraumaGap negotiation ∧
    0 < meshRoutingPaths mesh ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh ∧
      boundary.serviceRate =
        quorumSize (replicaCount (mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh))
          (mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh) := by
  exact ⟨mediation.hMediatorLoss,
    batna_trauma_gap_positive negotiation,
    mesh_routing_paths_positive mesh,
    ⟨canonicalQueueBoundary (mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh),
      rfl, rfl, rfl, rfl⟩⟩

theorem mediation_negotiation_spiderweb_budget_yields_positive_topological_deficit
    (mediation : MediationSetup) (negotiation : NegotiationSetup) (mesh : MeshConfig) :
    0 < topologicalDeficit
      (mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh + 1) 1 := by
  unfold topologicalDeficit
  rw [Nat.add_sub_cancel]
  exact mediation_negotiation_spiderweb_budget_positive mediation negotiation mesh

theorem mediation_negotiation_spiderweb_budget_does_not_force_zero_arrival
    (mediation : MediationSetup) (negotiation : NegotiationSetup) (mesh : MeshConfig) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh →
        boundary.serviceRate =
          quorumSize (replicaCount (mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh))
            (mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh) →
        boundary.arrivalRate = 0) := by
  intro hAll
  let boundary := canonicalQueueBoundary (mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh)
  have hZero := hAll boundary rfl rfl
  exact (Nat.ne_of_gt
    (mediation_negotiation_spiderweb_budget_positive mediation negotiation mesh)) hZero

theorem mediation_negotiation_spiderweb_budget_does_not_force_beta1_equals_budget
    (mediation : MediationSetup) (negotiation : NegotiationSetup) (mesh : MeshConfig) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh →
        boundary.serviceRate =
          quorumSize (replicaCount (mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh))
            (mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh) →
        boundary.beta1 = mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh) := by
  intro hAll
  let boundary := canonicalQueueBoundary (mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh)
  have hEq := hAll boundary rfl rfl
  have hZero :
      mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh = 0 :=
    Eq.symm hEq
  exact (Nat.ne_of_gt
    (mediation_negotiation_spiderweb_budget_positive mediation negotiation mesh)) hZero

theorem mediation_negotiation_spiderweb_semantic_morphism_yields_positive_topological_deficit
    (mediation : MediationSetup) (negotiation : NegotiationSetup) (mesh : MeshConfig)
    (interpret : Nat → Nat)
    (hInterpret :
      interpret (mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh + 1) =
        mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh + 1) :
    0 < topologicalDeficit
      (interpret (mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh + 1)) 1 := by
  rw [hInterpret]
  exact mediation_negotiation_spiderweb_budget_yields_positive_topological_deficit
    mediation
    negotiation
    mesh

theorem mediation_negotiation_spiderweb_budget_yields_geometric_rate_certificate
    (mediation : MediationSetup) (negotiation : NegotiationSetup) (mesh : MeshConfig) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh) ∧
      rate.initialBound = mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨budgetGeometricRate (mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate
      (mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh)).hRateLtOne
  · exact (budgetGeometricRate
      (mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh)).hInitialBoundPos

structure MediationNegotiationSpiderwebKernelLiftAdapter where
  mediation : MediationSetup
  negotiation : NegotiationSetup
  mesh : MeshConfig
  budget : Nat
  hBudgetEq : budget = mediationNegotiationSpiderwebFailureBudget mediation negotiation mesh
  driftGap : Nat
  hDriftGap : 0 < driftGap
deriving Repr

namespace MediationNegotiationSpiderwebKernelLiftAdapter

theorem budget_pos_from_source
    (adapter : MediationNegotiationSpiderwebKernelLiftAdapter) :
    0 < adapter.budget := by
  rw [adapter.hBudgetEq]
  exact mediation_negotiation_spiderweb_budget_positive
    adapter.mediation
    adapter.negotiation
    adapter.mesh

theorem mediation_negotiation_spiderweb_continuous_ergodicity_lift
    (adapter : MediationNegotiationSpiderwebKernelLiftAdapter) :
    adapter.budget =
      mediationNegotiationSpiderwebFailureBudget
        adapter.mediation
        adapter.negotiation
        adapter.mesh ∧
    0 < adapter.budget ∧
    0 < adapter.driftGap :=
  ⟨adapter.hBudgetEq, budget_pos_from_source adapter, adapter.hDriftGap⟩

end MediationNegotiationSpiderwebKernelLiftAdapter

end MediationNegotiationSpiderwebQueueKernelBridge
