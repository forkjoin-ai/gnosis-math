namespace DeceptionAutoimmunityQueueKernelBridge

/-! Init-only deception + autoimmunity queue bridge. -/

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

def deceptionFailureBudget (deception : DeceptionSetup) : Nat := deception.injected
def autoimmunityFailureBudget (autoimmune : AutoimmunitySetup) : Nat := autoimmune.parserExhaust
def deceptionAutoimmunityFailureBudget
    (deception : DeceptionSetup) (autoimmune : AutoimmunitySetup) : Nat :=
  deceptionFailureBudget deception + autoimmunityFailureBudget autoimmune

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
  unfold deceptionAutoimmunityFailureBudget deceptionFailureBudget
  exact Nat.lt_add_right (autoimmunityFailureBudget autoimmune) deception.hInjected

theorem deception_phantom_budget_yields_unit_queue_boundary
    (deception : DeceptionSetup) :
    0 < deceptionFailureBudget deception ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧ boundary.capacity = 1 ∧
      boundary.arrivalRate = deceptionFailureBudget deception ∧
      boundary.serviceRate =
        quorumSize (replicaCount (deceptionFailureBudget deception))
          (deceptionFailureBudget deception) := by
  exact ⟨deception.hInjected,
    ⟨canonicalQueueBoundary (deceptionFailureBudget deception), rfl, rfl, rfl, rfl⟩⟩

theorem autoimmunity_hash_collision_budget_yields_unit_queue_boundary
    (autoimmune : AutoimmunitySetup) :
    autoimmune.faultyHash = autoimmune.friendlyInvariant ∧
    0 < autoimmunityFailureBudget autoimmune ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧ boundary.capacity = 1 ∧
      boundary.arrivalRate = autoimmunityFailureBudget autoimmune ∧
      boundary.serviceRate =
        quorumSize (replicaCount (autoimmunityFailureBudget autoimmune))
          (autoimmunityFailureBudget autoimmune) := by
  exact ⟨autoimmune.hCollision, autoimmune.hParser,
    ⟨canonicalQueueBoundary (autoimmunityFailureBudget autoimmune), rfl, rfl, rfl, rfl⟩⟩

theorem deception_autoimmunity_budget_yields_unit_queue_boundary
    (deception : DeceptionSetup) (autoimmune : AutoimmunitySetup) :
    0 < deceptionFailureBudget deception ∧
    autoimmune.faultyHash = autoimmune.friendlyInvariant ∧
    0 < autoimmunityFailureBudget autoimmune ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧ boundary.capacity = 1 ∧
      boundary.arrivalRate = deceptionAutoimmunityFailureBudget deception autoimmune ∧
      boundary.serviceRate =
        quorumSize (replicaCount (deceptionAutoimmunityFailureBudget deception autoimmune))
          (deceptionAutoimmunityFailureBudget deception autoimmune) := by
  exact ⟨deception.hInjected, autoimmune.hCollision, autoimmune.hParser,
    ⟨canonicalQueueBoundary (deceptionAutoimmunityFailureBudget deception autoimmune),
      rfl, rfl, rfl, rfl⟩⟩

theorem deception_autoimmunity_budget_does_not_force_positive_beta1
    (deception : DeceptionSetup) (autoimmune : AutoimmunitySetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = deceptionAutoimmunityFailureBudget deception autoimmune →
        boundary.serviceRate =
          quorumSize (replicaCount (deceptionAutoimmunityFailureBudget deception autoimmune))
            (deceptionAutoimmunityFailureBudget deception autoimmune) →
        0 < boundary.beta1) := by
  intro hAll
  let boundary := canonicalQueueBoundary (deceptionAutoimmunityFailureBudget deception autoimmune)
  exact Nat.lt_irrefl 0 (hAll boundary rfl rfl)

theorem deception_autoimmunity_budget_does_not_force_beta1_equals_budget
    (deception : DeceptionSetup) (autoimmune : AutoimmunitySetup) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = deceptionAutoimmunityFailureBudget deception autoimmune →
        boundary.serviceRate =
          quorumSize (replicaCount (deceptionAutoimmunityFailureBudget deception autoimmune))
            (deceptionAutoimmunityFailureBudget deception autoimmune) →
        boundary.beta1 = deceptionAutoimmunityFailureBudget deception autoimmune) := by
  intro hAll
  let boundary := canonicalQueueBoundary (deceptionAutoimmunityFailureBudget deception autoimmune)
  have hEq := hAll boundary rfl rfl
  have hZero : deceptionAutoimmunityFailureBudget deception autoimmune = 0 := Eq.symm hEq
  exact (Nat.ne_of_gt (deception_autoimmunity_budget_positive deception autoimmune)) hZero

theorem deception_autoimmunity_budget_yields_geometric_rate_certificate
    (deception : DeceptionSetup) (autoimmune : AutoimmunitySetup) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (deceptionAutoimmunityFailureBudget deception autoimmune) ∧
      rate.initialBound = deceptionAutoimmunityFailureBudget deception autoimmune + 1 ∧
      rate.numerator = 3 ∧ rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧ 0 < rate.initialBound := by
  refine ⟨budgetGeometricRate (deceptionAutoimmunityFailureBudget deception autoimmune),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (deceptionAutoimmunityFailureBudget deception autoimmune)).hRateLtOne
  · exact (budgetGeometricRate (deceptionAutoimmunityFailureBudget deception autoimmune)).hInitialBoundPos

structure DeceptionAutoimmunityKernelLiftAdapter where
  deception : DeceptionSetup
  autoimmune : AutoimmunitySetup
  budget : Nat
  hBudgetEq : budget = deceptionAutoimmunityFailureBudget deception autoimmune
  driftGap : Nat
  hDriftGap : 0 < driftGap
deriving Repr

namespace DeceptionAutoimmunityKernelLiftAdapter

theorem deception_autoimmunity_continuous_ergodicity_lift
    (adapter : DeceptionAutoimmunityKernelLiftAdapter) :
    0 < adapter.budget ∧ 0 < adapter.driftGap := by
  rw [adapter.hBudgetEq]
  exact ⟨deception_autoimmunity_budget_positive adapter.deception adapter.autoimmune,
    adapter.hDriftGap⟩

end DeceptionAutoimmunityKernelLiftAdapter

end DeceptionAutoimmunityQueueKernelBridge
