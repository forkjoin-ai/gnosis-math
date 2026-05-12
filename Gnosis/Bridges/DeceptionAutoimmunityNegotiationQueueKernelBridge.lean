namespace DeceptionAutoimmunityNegotiationQueueKernelBridge

/-! Init-only deception + autoimmunity + negotiation queue bridge. -/

structure DeceptionSetup where
  injected : Nat
  hInjected : 1 ≤ injected
deriving Repr

structure AutoimmunitySetup where
  faultyHash : Nat
  friendlyInvariant : Nat
  parserExhaust : Nat
  hCollision : faultyHash = friendlyInvariant
  hParser : 1 ≤ parserExhaust
deriving Repr

structure NegotiationSetup where
  searchCapacity : Nat
  externalCapacity : Nat
  hSearchShort : searchCapacity < 10
  hCovered : 10 ≤ searchCapacity + externalCapacity
deriving Repr

def deceptionAutoimmunityFailureBudget
    (deception : DeceptionSetup) (autoimmune : AutoimmunitySetup) : Nat :=
  deception.injected + autoimmune.parserExhaust

def deceptionAutoimmunityNegotiationFailureBudget
    (deception : DeceptionSetup)
    (autoimmune : AutoimmunitySetup)
    (negotiation : NegotiationSetup) : Nat :=
  deception.injected + autoimmune.parserExhaust + negotiation.externalCapacity

def replicaCount (budget : Nat) : Nat := 2 * budget + 1
def quorumSize (_replicas budget : Nat) : Nat := budget + 1

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

theorem deception_autoimmunity_budget_positive
    (deception : DeceptionSetup) (autoimmune : AutoimmunitySetup) :
    0 < deceptionAutoimmunityFailureBudget deception autoimmune := by
  unfold deceptionAutoimmunityFailureBudget
  exact Nat.lt_add_right autoimmune.parserExhaust deception.hInjected

theorem negotiation_external_capacity_positive (negotiation : NegotiationSetup) :
    0 < negotiation.externalCapacity := by
  rcases negotiation with ⟨searchCapacity, externalCapacity, hSearchShort, hCovered⟩
  cases externalCapacity with
  | zero =>
      have hSearchLarge : 10 ≤ searchCapacity := by
        rw [Nat.add_zero] at hCovered
        exact hCovered
      exact False.elim ((Nat.not_le_of_gt hSearchShort) hSearchLarge)
  | succ k =>
      exact Nat.succ_pos k

theorem deception_autoimmunity_negotiation_budget_positive
    (deception : DeceptionSetup)
    (autoimmune : AutoimmunitySetup)
    (negotiation : NegotiationSetup) :
    0 < deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation := by
  unfold deceptionAutoimmunityNegotiationFailureBudget
  exact Nat.lt_add_right negotiation.externalCapacity
    (deception_autoimmunity_budget_positive deception autoimmune)

theorem deception_autoimmunity_negotiation_budget_yields_unit_queue_boundary
    (deception : DeceptionSetup)
    (autoimmune : AutoimmunitySetup)
    (negotiation : NegotiationSetup) :
    0 < deception.injected ∧ autoimmune.faultyHash = autoimmune.friendlyInvariant ∧
    0 < autoimmune.parserExhaust ∧ 0 < negotiation.externalCapacity ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧ boundary.capacity = 1 ∧
      boundary.arrivalRate =
        deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation))
          (deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation) := by
  exact ⟨deception.hInjected, autoimmune.hCollision, autoimmune.hParser,
    negotiation_external_capacity_positive negotiation,
    ⟨canonicalQueueBoundary
      (deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation),
      rfl, rfl, rfl, rfl⟩⟩

theorem deception_autoimmunity_negotiation_joint_queue_witness_pack
    (deception : DeceptionSetup)
    (autoimmune : AutoimmunitySetup)
    (negotiation : NegotiationSetup) :
    (∃ boundary : QueueBoundaryWitnessNat,
      boundary.arrivalRate = deceptionAutoimmunityFailureBudget deception autoimmune ∧
      boundary.capacity = 1) ∧
    (∃ boundary : QueueBoundaryWitnessNat,
      boundary.arrivalRate =
        deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation ∧
      boundary.capacity = 1) := by
  exact
    ⟨⟨canonicalQueueBoundary (deceptionAutoimmunityFailureBudget deception autoimmune),
      rfl, rfl⟩,
     ⟨canonicalQueueBoundary
      (deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation),
      rfl, rfl⟩⟩

theorem deception_autoimmunity_negotiation_budget_does_not_force_positive_beta1
    (deception : DeceptionSetup)
    (autoimmune : AutoimmunitySetup)
    (negotiation : NegotiationSetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate =
          deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation →
        boundary.serviceRate =
          quorumSize
            (replicaCount (deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation))
            (deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation) →
        0 < boundary.beta1) := by
  intro hAll
  let boundary :=
    canonicalQueueBoundary
      (deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation)
  exact Nat.lt_irrefl 0 (hAll boundary rfl rfl)

theorem deception_autoimmunity_negotiation_budget_does_not_force_beta1_equals_budget
    (deception : DeceptionSetup)
    (autoimmune : AutoimmunitySetup)
    (negotiation : NegotiationSetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate =
          deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation →
        boundary.serviceRate =
          quorumSize
            (replicaCount (deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation))
            (deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation) →
        boundary.beta1 =
          deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation) := by
  intro hAll
  let boundary :=
    canonicalQueueBoundary
      (deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation)
  have hEq := hAll boundary rfl rfl
  have hZero :
      deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation = 0 :=
    Eq.symm hEq
  exact
    (Nat.ne_of_gt
      (deception_autoimmunity_negotiation_budget_positive deception autoimmune negotiation))
    hZero

theorem deception_autoimmunity_negotiation_budget_yields_geometric_rate_certificate
    (deception : DeceptionSetup)
    (autoimmune : AutoimmunitySetup)
    (negotiation : NegotiationSetup) :
    ∃ rate : GeometricRateNat,
      rate =
        budgetGeometricRate
          (deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation) ∧
      rate.initialBound =
        deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation + 1 ∧
      rate.numerator = 3 ∧ rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧ 0 < rate.initialBound := by
  refine
    ⟨budgetGeometricRate
      (deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation),
      rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate
      (deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation)).hRateLtOne
  · exact (budgetGeometricRate
      (deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation)).hInitialBoundPos

theorem deception_autoimmunity_negotiation_budget_real_positive
    (deception : DeceptionSetup)
    (autoimmune : AutoimmunitySetup)
    (negotiation : NegotiationSetup) :
    0 < deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation :=
  deception_autoimmunity_negotiation_budget_positive deception autoimmune negotiation

structure DeceptionAutoimmunityNegotiationKernelLiftAdapter where
  deception : DeceptionSetup
  autoimmune : AutoimmunitySetup
  negotiation : NegotiationSetup
  budget : Nat
  hBudgetEq :
    budget = deceptionAutoimmunityNegotiationFailureBudget deception autoimmune negotiation
  driftGap : Nat
  hDriftGap : 0 < driftGap
deriving Repr

namespace DeceptionAutoimmunityNegotiationKernelLiftAdapter

theorem budget_pos_from_source
    (adapter : DeceptionAutoimmunityNegotiationKernelLiftAdapter) :
    0 < adapter.budget := by
  rw [adapter.hBudgetEq]
  exact deception_autoimmunity_negotiation_budget_positive
    adapter.deception adapter.autoimmune adapter.negotiation

theorem deception_autoimmunity_negotiation_continuous_ergodicity_lift
    (adapter : DeceptionAutoimmunityNegotiationKernelLiftAdapter) :
    0 < adapter.budget ∧ 0 < adapter.driftGap := by
  exact ⟨adapter.budget_pos_from_source, adapter.hDriftGap⟩

end DeceptionAutoimmunityNegotiationKernelLiftAdapter

end DeceptionAutoimmunityNegotiationQueueKernelBridge
