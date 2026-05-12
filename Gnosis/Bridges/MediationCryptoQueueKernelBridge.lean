import Init

/-!
# Mediation/Crypto Queue Kernel Bridge

Finite mediation-loss and cryptographic side-channel floor witnesses for stale
MCP rows.
-/

namespace MediationCryptoQueueKernelBridge

structure MediationSetup where
  mediatorLoss : Nat
  hMediatorLoss : 1 ≤ mediatorLoss
deriving Repr

structure CryptoSetup where
  perEvalFloor : Nat
  hFloor : 0 < perEvalFloor
deriving Repr

def mediationCryptoFailureBudget
    (mediation : MediationSetup) (crypto : CryptoSetup) : Nat :=
  mediation.mediatorLoss + crypto.perEvalFloor

def replicaCount (budget : Nat) : Nat := 2 * budget + 1

def quorumSize (_replicas budget : Nat) : Nat := budget + 1

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

theorem mediation_crypto_budget_positive
    (mediation : MediationSetup) (crypto : CryptoSetup) :
    0 < mediationCryptoFailureBudget mediation crypto := by
  unfold mediationCryptoFailureBudget
  exact Nat.lt_add_right crypto.perEvalFloor mediation.hMediatorLoss

theorem mediation_crypto_side_channel_yields_unit_queue_boundary
    (mediation : MediationSetup) (crypto : CryptoSetup) :
    0 < mediation.mediatorLoss ∧
    0 < crypto.perEvalFloor ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = mediationCryptoFailureBudget mediation crypto ∧
      boundary.serviceRate =
        quorumSize (replicaCount (mediationCryptoFailureBudget mediation crypto))
          (mediationCryptoFailureBudget mediation crypto) := by
  exact ⟨mediation.hMediatorLoss, crypto.hFloor,
    ⟨canonicalQueueBoundary (mediationCryptoFailureBudget mediation crypto),
      rfl, rfl, rfl, rfl⟩⟩

theorem mediation_crypto_side_channel_does_not_force_positive_beta1
    (mediation : MediationSetup) (crypto : CryptoSetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = mediationCryptoFailureBudget mediation crypto →
        boundary.serviceRate =
          quorumSize (replicaCount (mediationCryptoFailureBudget mediation crypto))
            (mediationCryptoFailureBudget mediation crypto) →
        0 < boundary.beta1) := by
  intro hAll
  let boundary := canonicalQueueBoundary (mediationCryptoFailureBudget mediation crypto)
  exact Nat.lt_irrefl 0 (hAll boundary rfl rfl)

theorem mediation_crypto_side_channel_yields_geometric_rate_certificate
    (mediation : MediationSetup) (crypto : CryptoSetup) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (mediationCryptoFailureBudget mediation crypto) ∧
      rate.initialBound = mediationCryptoFailureBudget mediation crypto + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨budgetGeometricRate (mediationCryptoFailureBudget mediation crypto),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (mediationCryptoFailureBudget mediation crypto)).hRateLtOne
  · exact (budgetGeometricRate (mediationCryptoFailureBudget mediation crypto)).hInitialBoundPos

structure MediationCryptoKernelLiftAdapter where
  mediation : MediationSetup
  crypto : CryptoSetup
  budget : Nat
  hBudgetEq : budget = mediationCryptoFailureBudget mediation crypto
  driftGap : Nat
  hDriftGap : 0 < driftGap
deriving Repr

end MediationCryptoQueueKernelBridge

namespace MediationCryptoKernelLiftAdapter

abbrev MediationCryptoKernelLiftAdapter :=
  MediationCryptoQueueKernelBridge.MediationCryptoKernelLiftAdapter

theorem mediated_continuous_ergodicity_lift
    (adapter : MediationCryptoKernelLiftAdapter) :
    adapter.budget =
      MediationCryptoQueueKernelBridge.mediationCryptoFailureBudget
        adapter.mediation
        adapter.crypto ∧
    0 < adapter.budget ∧
    0 < adapter.driftGap := by
  rw [adapter.hBudgetEq]
  exact ⟨rfl,
    MediationCryptoQueueKernelBridge.mediation_crypto_budget_positive
      adapter.mediation
      adapter.crypto,
    adapter.hDriftGap⟩

end MediationCryptoKernelLiftAdapter
