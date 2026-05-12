import Gnosis.SleepQuorumQueueMoonshots
import Gnosis.Bridges.SleepDebtQuorumErgodicityBridge

/-!
# Sleep-Debt Quorum Queue Bridge

Compatibility bridge for weighted sleep-debt MCP rows that still pointed at the
old bridge filename. The proofs reuse the Init-only weighted-schedule and
quorum-embedding chapel modules.
-/

namespace SleepDebtQuorumQueueBridge

def weightedDebt
    (cycleLength scheduledWake wakeBurdenRate recoveryRate n : Nat) : Nat :=
  Gnosis.SleepDebtWeightedSchedule.iteratedDebt
    n cycleLength scheduledWake wakeBurdenRate recoveryRate

abbrev QueueBoundaryWitnessNat :=
  Gnosis.QueueBoundaryWitnessNat_SleepQuorumQueueMoonshots

abbrev GeometricRateNat :=
  Gnosis.GeometricErgodicityRateNat_SleepQuorumQueueMoonshots

abbrev MultiLevelHarrisWitnessNat :=
  Gnosis.MultiLevelHarrisWitnessNat_SleepQuorumQueueMoonshots

theorem positive_weighted_sleep_debt_yields_strict_majority_embedding
    {cycleLength scheduledWake wakeBurdenRate recoveryRate n : Nat}
    (hCrossed :
      Gnosis.SleepDebtWeightedSchedule.thresholdRhs cycleLength recoveryRate <
        Gnosis.SleepDebtWeightedSchedule.thresholdLhs
          scheduledWake wakeBurdenRate recoveryRate)
    (hCycle : 0 < n) :
    let debt := weightedDebt cycleLength scheduledWake wakeBurdenRate recoveryRate n
    0 < debt ∧
      2 * Gnosis.canonicalFailureBudgetFromDebt debt <
        Gnosis.canonicalReplicaCountFromDebt debt := by
  intro debt
  exact Gnosis.positive_weighted_sleep_debt_yields_strict_majority_embedding
    hCrossed hCycle

theorem positive_weighted_sleep_debt_embedding_implies_failure_budget_lt_quorum
    {cycleLength scheduledWake wakeBurdenRate recoveryRate n : Nat}
    (_hCrossed :
      Gnosis.SleepDebtWeightedSchedule.thresholdRhs cycleLength recoveryRate <
        Gnosis.SleepDebtWeightedSchedule.thresholdLhs
          scheduledWake wakeBurdenRate recoveryRate)
    (_hCycle : 0 < n) :
    let debt := weightedDebt cycleLength scheduledWake wakeBurdenRate recoveryRate n
    Gnosis.canonicalFailureBudgetFromDebt debt <
      Gnosis.canonicalReplicaCountFromDebt debt := by
  intro debt
  unfold Gnosis.canonicalFailureBudgetFromDebt
    Gnosis.canonicalReplicaCountFromDebt
  rw [Nat.two_mul]
  exact Nat.lt_succ_of_le (Nat.le_add_left debt debt)

theorem weighted_sleep_debt_quorum_embedding_yields_unit_queue_boundary
    {cycleLength scheduledWake wakeBurdenRate recoveryRate n : Nat}
    (hCrossed :
      Gnosis.SleepDebtWeightedSchedule.thresholdRhs cycleLength recoveryRate <
        Gnosis.SleepDebtWeightedSchedule.thresholdLhs
          scheduledWake wakeBurdenRate recoveryRate)
    (hCycle : 0 < n) :
    let debt := weightedDebt cycleLength scheduledWake wakeBurdenRate recoveryRate n
    0 < debt ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = Gnosis.canonicalFailureBudgetFromDebt debt ∧
      boundary.serviceRate =
        Gnosis.quorumSize (Gnosis.canonicalReplicaCountFromDebt debt)
          (Gnosis.canonicalFailureBudgetFromDebt debt) := by
  intro debt
  refine ⟨?_, ?_⟩
  · exact Gnosis.SleepDebtWeightedSchedule.iterated_debt_positive_above_threshold
      hCrossed hCycle
  · exact Gnosis.positive_weighted_sleep_debt_via_quorum_embedding_yields_unit_capacity_boundary
      hCrossed hCycle

theorem positive_weighted_sleep_debt_yields_geometric_rate_certificate
    {cycleLength scheduledWake wakeBurdenRate recoveryRate n : Nat}
    (hCrossed :
      Gnosis.SleepDebtWeightedSchedule.thresholdRhs cycleLength recoveryRate <
        Gnosis.SleepDebtWeightedSchedule.thresholdLhs
          scheduledWake wakeBurdenRate recoveryRate)
    (hCycle : 0 < n) :
    let debt := weightedDebt cycleLength scheduledWake wakeBurdenRate recoveryRate n
    0 < debt ∧
    ∃ rate : GeometricRateNat,
      rate = Gnosis.debtIndexedGeometricRate debt ∧
      rate.initialBound = debt + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 := by
  intro debt
  exact Gnosis.positive_weighted_sleep_debt_yields_geometric_rate_certificate
    hCrossed hCycle

theorem positive_weighted_sleep_debt_yields_multilevel_harris_witness
    {cycleLength scheduledWake wakeBurdenRate recoveryRate n : Nat}
    (hCrossed :
      Gnosis.SleepDebtWeightedSchedule.thresholdRhs cycleLength recoveryRate <
        Gnosis.SleepDebtWeightedSchedule.thresholdLhs
          scheduledWake wakeBurdenRate recoveryRate)
    (hCycle : 0 < n) :
    ∃ witness : MultiLevelHarrisWitnessNat,
      0 < witness.discreteDriftGap ∧
      0 < witness.continuousDriftGap :=
  Gnosis.positive_weighted_sleep_debt_yields_multilevel_harris_witness
    hCrossed hCycle

theorem positive_weighted_sleep_debt_can_coexist_with_non_majority_quorum :
    ∃ cycleLength scheduledWake wakeBurdenRate recoveryRate n replicaCount failureBudget : Nat,
      Gnosis.SleepDebtWeightedSchedule.thresholdRhs cycleLength recoveryRate <
          Gnosis.SleepDebtWeightedSchedule.thresholdLhs
            scheduledWake wakeBurdenRate recoveryRate ∧
      0 < n ∧
      0 < weightedDebt cycleLength scheduledWake wakeBurdenRate recoveryRate n ∧
      ¬ (2 * failureBudget < replicaCount) :=
  Gnosis.positive_weighted_sleep_debt_can_coexist_with_nonmajority_quorum

end SleepDebtQuorumQueueBridge
