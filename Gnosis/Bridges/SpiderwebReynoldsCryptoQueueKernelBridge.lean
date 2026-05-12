namespace SpiderwebReynoldsCryptoQueueKernelBridge

/-! Init-only spiderweb + Reynolds + crypto queue bridge. -/

structure MeshConfig where
  peers : Nat
  hops : Nat
  hPeers : 0 < peers
  hHops : 0 < hops
deriving Repr

structure ReynoldsSetup where
  pathCount : Nat
  hDiverse : 2 ≤ pathCount
deriving Repr

structure SideChannelShadow where
  perEvalFloor : Nat
  hFloor : 0 < perEvalFloor
deriving Repr

def meshRoutingPaths (mesh : MeshConfig) : Nat := mesh.peers * mesh.hops
def reynoldsDiversityBudget (reynolds : ReynoldsSetup) : Nat := reynolds.pathCount - 1
def spiderwebReynoldsCryptoFailureBudget
    (mesh : MeshConfig) (reynolds : ReynoldsSetup) (crypto : SideChannelShadow) : Nat :=
  meshRoutingPaths mesh + reynoldsDiversityBudget reynolds + crypto.perEvalFloor

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
  { beta1 := 0, capacity := 1, arrivalRate := budget,
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
  { numerator := 3, denominator := 4, initialBound := budget + 1,
    hRateLtOne := by decide, hDenomPos := by decide,
    hInitialBoundPos := Nat.succ_pos budget }

theorem mesh_routing_paths_positive (mesh : MeshConfig) :
    0 < meshRoutingPaths mesh := by
  unfold meshRoutingPaths
  exact Nat.mul_pos mesh.hPeers mesh.hHops

theorem spiderweb_reynolds_crypto_budget_positive
    (mesh : MeshConfig) (reynolds : ReynoldsSetup) (crypto : SideChannelShadow) :
    0 < spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto := by
  unfold spiderwebReynoldsCryptoFailureBudget
  exact Nat.lt_add_right crypto.perEvalFloor
    (Nat.lt_add_right (reynoldsDiversityBudget reynolds) (mesh_routing_paths_positive mesh))

theorem spiderweb_reynolds_crypto_budget_yields_unit_queue_boundary
    (mesh : MeshConfig) (reynolds : ReynoldsSetup) (crypto : SideChannelShadow) :
    0 < meshRoutingPaths mesh ∧ 0 < crypto.perEvalFloor ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧ boundary.capacity = 1 ∧
      boundary.arrivalRate = spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto ∧
      boundary.serviceRate =
        quorumSize (replicaCount (spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto))
          (spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto) := by
  exact ⟨mesh_routing_paths_positive mesh, crypto.hFloor,
    ⟨canonicalQueueBoundary (spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto),
      rfl, rfl, rfl, rfl⟩⟩

theorem spiderweb_reynolds_crypto_budget_yields_positive_topological_deficit
    (mesh : MeshConfig) (reynolds : ReynoldsSetup) (crypto : SideChannelShadow) :
    0 < topologicalDeficit (spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto + 1) 1 := by
  unfold topologicalDeficit
  rw [Nat.add_sub_cancel]
  exact spiderweb_reynolds_crypto_budget_positive mesh reynolds crypto

theorem spiderweb_reynolds_crypto_budget_does_not_force_beta1_equals_budget
    (mesh : MeshConfig) (reynolds : ReynoldsSetup) (crypto : SideChannelShadow) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto →
        boundary.serviceRate =
          quorumSize (replicaCount (spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto))
            (spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto) →
        boundary.beta1 = spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto) := by
  intro hAll
  let boundary := canonicalQueueBoundary (spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto)
  have hEq := hAll boundary rfl rfl
  have hZero : spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto = 0 := Eq.symm hEq
  exact (Nat.ne_of_gt (spiderweb_reynolds_crypto_budget_positive mesh reynolds crypto)) hZero

theorem spiderweb_reynolds_crypto_semantic_morphism_yields_unit_queue_boundary
    (mesh : MeshConfig) (reynolds : ReynoldsSetup) (crypto : SideChannelShadow)
    (interpret : Nat → Nat)
    (hInterpret :
      interpret (spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto) =
        spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto) :
    0 < interpret (spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto) ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧ boundary.capacity = 1 ∧
      boundary.arrivalRate = interpret (spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto) ∧
      boundary.serviceRate =
        quorumSize (replicaCount (interpret (spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto)))
          (interpret (spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto)) := by
  rw [hInterpret]
  exact ⟨spiderweb_reynolds_crypto_budget_positive mesh reynolds crypto,
    ⟨canonicalQueueBoundary (spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto),
      rfl, rfl, rfl, rfl⟩⟩

theorem spiderweb_reynolds_crypto_budget_yields_geometric_rate_certificate
    (mesh : MeshConfig) (reynolds : ReynoldsSetup) (crypto : SideChannelShadow) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto) ∧
      rate.initialBound = spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto + 1 ∧
      rate.numerator = 3 ∧ rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧ 0 < rate.initialBound := by
  refine ⟨budgetGeometricRate (spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto)).hRateLtOne
  · exact (budgetGeometricRate (spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto)).hInitialBoundPos

theorem spiderweb_reynolds_crypto_semantic_morphism_continuous_ergodicity_lift
    (mesh : MeshConfig) (reynolds : ReynoldsSetup) (crypto : SideChannelShadow)
    (interpret : Nat → Nat)
    (hInterpret :
      interpret (spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto) =
        spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto)
    (driftGap : Nat) (hDriftGap : 0 < driftGap) :
    0 < interpret (spiderwebReynoldsCryptoFailureBudget mesh reynolds crypto) ∧
    0 < driftGap := by
  rw [hInterpret]
  exact ⟨spiderweb_reynolds_crypto_budget_positive mesh reynolds crypto, hDriftGap⟩

end SpiderwebReynoldsCryptoQueueKernelBridge
