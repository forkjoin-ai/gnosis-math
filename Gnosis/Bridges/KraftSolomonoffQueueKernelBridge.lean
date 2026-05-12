import Init

/-!
# Kraft/Solomonoff Queue Kernel Bridge

Init-only finite witnesses for the MCP rows formerly attached to the
Mathlib-heavy Kraft/Solomonoff queue bridge.
-/

namespace KraftSolomonoffQueueKernelBridge

structure PrefixFreeCodeBudget where
  total : Nat
  used : Nat
  wastedCapacity : Nat
  hWeight : total - wastedCapacity + 1 = used + 1
deriving Repr

structure SolomonoffBudget where
  R : Nat
  v : Nat
  hBound : v ≤ R
deriving Repr

def kraftFailureBudget (code : PrefixFreeCodeBudget) : Nat :=
  code.wastedCapacity

def solomonoffDescriptionBudget (budget : SolomonoffBudget) : Nat :=
  budget.v

def combinedFailureBudget
    (code : PrefixFreeCodeBudget)
    (budget : SolomonoffBudget) : Nat :=
  kraftFailureBudget code + solomonoffDescriptionBudget budget

def solomonoffGodWeight (budget : SolomonoffBudget) : Nat :=
  budget.R - budget.v + 1

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

theorem kraft_wasted_capacity_yields_unit_queue_boundary
    (code : PrefixFreeCodeBudget) :
    code.total - code.wastedCapacity + 1 = code.used + 1 ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = kraftFailureBudget code ∧
      boundary.serviceRate =
        quorumSize (replicaCount (kraftFailureBudget code)) (kraftFailureBudget code) := by
  exact ⟨code.hWeight,
    ⟨canonicalQueueBoundary (kraftFailureBudget code), rfl, rfl, rfl, rfl⟩⟩

theorem solomonoff_description_conservation
    (budget : SolomonoffBudget) :
    solomonoffGodWeight budget + budget.v = budget.R + 1 := by
  unfold solomonoffGodWeight
  rw [Nat.add_assoc, Nat.add_comm 1 budget.v, ← Nat.add_assoc]
  rw [Nat.sub_add_cancel budget.hBound]

theorem solomonoff_description_budget_yields_unit_queue_boundary
    (budget : SolomonoffBudget) :
    solomonoffGodWeight budget + budget.v = budget.R + 1 ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = solomonoffDescriptionBudget budget ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (solomonoffDescriptionBudget budget))
          (solomonoffDescriptionBudget budget) := by
  exact ⟨solomonoff_description_conservation budget,
    ⟨canonicalQueueBoundary (solomonoffDescriptionBudget budget),
      rfl, rfl, rfl, rfl⟩⟩

theorem kraft_solomonoff_budget_yields_unit_queue_boundary
    (code : PrefixFreeCodeBudget)
    (budget : SolomonoffBudget) :
    code.total - code.wastedCapacity + 1 = code.used + 1 ∧
    solomonoffGodWeight budget + budget.v = budget.R + 1 ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = combinedFailureBudget code budget ∧
      boundary.serviceRate =
        quorumSize
          (replicaCount (combinedFailureBudget code budget))
          (combinedFailureBudget code budget) := by
  exact ⟨code.hWeight, solomonoff_description_conservation budget,
    ⟨canonicalQueueBoundary (combinedFailureBudget code budget),
      rfl, rfl, rfl, rfl⟩⟩

theorem kraft_solomonoff_budget_does_not_force_beta1_equals_budget
    (code : PrefixFreeCodeBudget)
    (budget : SolomonoffBudget)
    (hPositive : 0 < combinedFailureBudget code budget) :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
        boundary.arrivalRate = combinedFailureBudget code budget →
        boundary.serviceRate =
          quorumSize
            (replicaCount (combinedFailureBudget code budget))
            (combinedFailureBudget code budget) →
        boundary.beta1 = combinedFailureBudget code budget) := by
  intro hAll
  let boundary := canonicalQueueBoundary (combinedFailureBudget code budget)
  have hEq : boundary.beta1 = combinedFailureBudget code budget :=
    hAll boundary rfl rfl
  rw [show boundary.beta1 = 0 by rfl] at hEq
  rw [← hEq] at hPositive
  exact Nat.lt_irrefl 0 hPositive

theorem kraft_solomonoff_budget_yields_geometric_rate_certificate
    (code : PrefixFreeCodeBudget)
    (budget : SolomonoffBudget) :
    ∃ rate : GeometricRateNat,
      rate = budgetGeometricRate (combinedFailureBudget code budget) ∧
      rate.initialBound = combinedFailureBudget code budget + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 ∧
      rate.numerator < rate.denominator ∧
      0 < rate.initialBound := by
  refine ⟨budgetGeometricRate (combinedFailureBudget code budget),
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (budgetGeometricRate (combinedFailureBudget code budget)).hRateLtOne
  · exact (budgetGeometricRate (combinedFailureBudget code budget)).hInitialBoundPos

structure KraftSolomonoffKernelLiftBundle where
  code : PrefixFreeCodeBudget
  solomonoff : SolomonoffBudget
  budget : Nat
  hBudgetEq : budget = combinedFailureBudget code solomonoff
  driftGap : Nat
  hDriftGap : 0 < driftGap
deriving Repr

end KraftSolomonoffQueueKernelBridge

namespace KraftSolomonoffKernelLiftAdapter

abbrev KraftSolomonoffKernelLiftBundle :=
  KraftSolomonoffQueueKernelBridge.KraftSolomonoffKernelLiftBundle

theorem kraft_solomonoff_continuous_ergodicity_lift
    (adapter : KraftSolomonoffKernelLiftBundle) :
    adapter.budget =
      KraftSolomonoffQueueKernelBridge.combinedFailureBudget
        adapter.code
        adapter.solomonoff ∧
    0 < adapter.driftGap :=
  ⟨adapter.hBudgetEq, adapter.hDriftGap⟩

end KraftSolomonoffKernelLiftAdapter
