namespace MediationCryptoNegotiationQueueKernelBridge

/-! Init-only mediation + crypto + negotiation queue bridge. -/

structure MediationSetup where
  mediatorLoss : Nat
  hMediatorLoss : 1 ≤ mediatorLoss
deriving Repr

structure CryptoSetup where
  perEvalFloor : Nat
  hFloor : 0 < perEvalFloor
deriving Repr

structure NegotiationSetup where
  untanglingWattsCost : Nat
  slamTraumaPenalty : Nat
  hPenalty : untanglingWattsCost + 1 ≤ slamTraumaPenalty
deriving Repr

def batnaTraumaGap (negotiation : NegotiationSetup) : Nat :=
  negotiation.slamTraumaPenalty - negotiation.untanglingWattsCost

def mediationCryptoNegotiationFailureBudget
    (mediation : MediationSetup) (crypto : CryptoSetup) (negotiation : NegotiationSetup) : Nat :=
  mediation.mediatorLoss + crypto.perEvalFloor + batnaTraumaGap negotiation

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

theorem batna_trauma_gap_positive (negotiation : NegotiationSetup) :
    0 < batnaTraumaGap negotiation := by
  unfold batnaTraumaGap
  exact Nat.sub_pos_of_lt negotiation.hPenalty

theorem mediation_crypto_negotiation_budget_positive
    (mediation : MediationSetup) (crypto : CryptoSetup) (negotiation : NegotiationSetup) :
    0 < mediationCryptoNegotiationFailureBudget mediation crypto negotiation := by
  unfold mediationCryptoNegotiationFailureBudget
  exact Nat.lt_add_right (batnaTraumaGap negotiation)
    (Nat.lt_add_right crypto.perEvalFloor mediation.hMediatorLoss)

theorem mediation_crypto_negotiation_budget_yields_unit_queue_boundary
    (mediation : MediationSetup) (crypto : CryptoSetup) (negotiation : NegotiationSetup) :
    0 < mediation.mediatorLoss ∧ 0 < crypto.perEvalFloor ∧
    0 < batnaTraumaGap negotiation ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧ boundary.capacity = 1 ∧
      boundary.arrivalRate = mediationCryptoNegotiationFailureBudget mediation crypto negotiation ∧
      boundary.serviceRate =
        quorumSize (replicaCount (mediationCryptoNegotiationFailureBudget mediation crypto negotiation))
          (mediationCryptoNegotiationFailureBudget mediation crypto negotiation) := by
  exact ⟨mediation.hMediatorLoss, crypto.hFloor, batna_trauma_gap_positive negotiation,
    ⟨canonicalQueueBoundary (mediationCryptoNegotiationFailureBudget mediation crypto negotiation),
      rfl, rfl, rfl, rfl⟩⟩

theorem mediation_crypto_negotiation_budget_yields_positive_topological_deficit
    (mediation : MediationSetup) (crypto : CryptoSetup) (negotiation : NegotiationSetup) :
    0 < topologicalDeficit
      (mediationCryptoNegotiationFailureBudget mediation crypto negotiation + 1) 1 := by
  unfold topologicalDeficit
  rw [Nat.add_sub_cancel]
  exact mediation_crypto_negotiation_budget_positive mediation crypto negotiation

theorem mediation_crypto_negotiation_budget_does_not_force_strict_capacity_growth
    (mediation : MediationSetup) (crypto : CryptoSetup) (negotiation : NegotiationSetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = mediationCryptoNegotiationFailureBudget mediation crypto negotiation →
        boundary.serviceRate =
          quorumSize (replicaCount (mediationCryptoNegotiationFailureBudget mediation crypto negotiation))
            (mediationCryptoNegotiationFailureBudget mediation crypto negotiation) →
        1 < boundary.capacity) := by
  intro hAll
  let boundary := canonicalQueueBoundary (mediationCryptoNegotiationFailureBudget mediation crypto negotiation)
  exact Nat.lt_irrefl 1 (hAll boundary rfl rfl)

theorem mediation_crypto_negotiation_budget_does_not_force_transport_match
    (mediation : MediationSetup) (crypto : CryptoSetup) (negotiation : NegotiationSetup) :
    ¬ (topologicalDeficit
        (mediationCryptoNegotiationFailureBudget mediation crypto negotiation + 1) 1 ≤ 0) := by
  intro hNonpositive
  exact Nat.not_lt_of_ge hNonpositive
    (mediation_crypto_negotiation_budget_yields_positive_topological_deficit
      mediation crypto negotiation)

theorem mediation_crypto_negotiation_budget_yields_geometric_rate_certificate
    (mediation : MediationSetup) (crypto : CryptoSetup) (negotiation : NegotiationSetup) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (mediationCryptoNegotiationFailureBudget mediation crypto negotiation) ∧
      rate.initialBound = mediationCryptoNegotiationFailureBudget mediation crypto negotiation + 1 ∧
      rate.numerator = 3 ∧ rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧ 0 < rate.initialBound := by
  refine ⟨budgetGeometricRate (mediationCryptoNegotiationFailureBudget mediation crypto negotiation),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate
      (mediationCryptoNegotiationFailureBudget mediation crypto negotiation)).hRateLtOne
  · exact (budgetGeometricRate
      (mediationCryptoNegotiationFailureBudget mediation crypto negotiation)).hInitialBoundPos

structure CompiledWitnessNat where
  budget : Nat
  atomMass : Nat
  minorizationMass : Nat
  driftGap : Nat
  hBudget : 0 < budget
  hAtom : 0 < atomMass
  hMinorization : 0 < minorizationMass
  hDriftGap : 0 < driftGap
deriving Repr

def mediationCryptoNegotiationCompileWitnessFromPrimitives
    (mediation : MediationSetup) (crypto : CryptoSetup) (negotiation : NegotiationSetup)
    (atomMass minorizationMass driftGap : Nat)
    (hAtom : 0 < atomMass)
    (hMinorization : 0 < minorizationMass)
    (hDriftGap : 0 < driftGap) : CompiledWitnessNat :=
  { budget := mediationCryptoNegotiationFailureBudget mediation crypto negotiation
    atomMass := atomMass
    minorizationMass := minorizationMass
    driftGap := driftGap
    hBudget := mediation_crypto_negotiation_budget_positive mediation crypto negotiation
    hAtom := hAtom
    hMinorization := hMinorization
    hDriftGap := hDriftGap }

theorem mediation_crypto_negotiation_compile_witness_from_primitives
    (mediation : MediationSetup) (crypto : CryptoSetup) (negotiation : NegotiationSetup)
    (atomMass minorizationMass driftGap : Nat)
    (hAtom : 0 < atomMass)
    (hMinorization : 0 < minorizationMass)
    (hDriftGap : 0 < driftGap) :
    ∃ witness : CompiledWitnessNat,
      witness.budget = mediationCryptoNegotiationFailureBudget mediation crypto negotiation ∧
      0 < witness.atomMass ∧ 0 < witness.minorizationMass ∧ 0 < witness.driftGap := by
  exact ⟨mediationCryptoNegotiationCompileWitnessFromPrimitives
      mediation crypto negotiation atomMass minorizationMass driftGap hAtom hMinorization hDriftGap,
    rfl, hAtom, hMinorization, hDriftGap⟩

theorem mediation_crypto_negotiation_compiled_witness_continuous_ergodicity_lift
    (mediation : MediationSetup) (crypto : CryptoSetup) (negotiation : NegotiationSetup)
    (atomMass minorizationMass driftGap : Nat)
    (hAtom : 0 < atomMass)
    (hMinorization : 0 < minorizationMass)
    (hDriftGap : 0 < driftGap) :
    ∃ witness : CompiledWitnessNat,
      0 < witness.budget ∧ 0 < witness.driftGap := by
  let witness :=
    mediationCryptoNegotiationCompileWitnessFromPrimitives
      mediation crypto negotiation atomMass minorizationMass driftGap
      hAtom hMinorization hDriftGap
  exact ⟨witness, witness.hBudget, witness.hDriftGap⟩

end MediationCryptoNegotiationQueueKernelBridge
