import Gnosis.SleepDebtWeightedSchedule
import Gnosis.FailureDurability

namespace Gnosis

/-!
Init-only sleep quorum queue moonshots.

`Nat`-typed contraction rate (via `(numerator, denominator)` pair) and Harris
witness; `QueueBoundaryWitness` rates are `Nat`-valued.
-/

def canonicalReplicaCountFromDebt (debt : Nat) : Nat := 2 * debt + 1
def canonicalFailureBudgetFromDebt (debt : Nat) : Nat := debt

theorem canonical_debt_embedding_strict_majority (debt : Nat) :
    2 * canonicalFailureBudgetFromDebt debt < canonicalReplicaCountFromDebt debt := by
  unfold canonicalFailureBudgetFromDebt canonicalReplicaCountFromDebt
  omega

theorem positive_weighted_sleep_debt_yields_strict_majority_embedding
    {cycleLength scheduledWake wakeBurdenRate recoveryRate n : Nat}
    (hCrossed :
      SleepDebtWeightedSchedule.thresholdRhs cycleLength recoveryRate <
        SleepDebtWeightedSchedule.thresholdLhs
          scheduledWake wakeBurdenRate recoveryRate)
    (hCycle : 0 < n) :
    let debt :=
      SleepDebtWeightedSchedule.iteratedDebt
        n cycleLength scheduledWake wakeBurdenRate recoveryRate
    0 < debt ∧
      2 * canonicalFailureBudgetFromDebt debt < canonicalReplicaCountFromDebt debt := by
  intro debt
  refine ⟨?_, canonical_debt_embedding_strict_majority debt⟩
  exact SleepDebtWeightedSchedule.iterated_debt_positive_above_threshold hCrossed hCycle

structure QueueBoundaryWitnessNat_SleepQuorumQueueMoonshots where
  beta1 : Nat
  capacity : Nat
  arrivalRate : Nat
  serviceRate : Nat

theorem positive_weighted_sleep_debt_via_quorum_embedding_yields_unit_capacity_boundary
    {cycleLength scheduledWake wakeBurdenRate recoveryRate n : Nat}
    (_hCrossed :
      SleepDebtWeightedSchedule.thresholdRhs cycleLength recoveryRate <
        SleepDebtWeightedSchedule.thresholdLhs
          scheduledWake wakeBurdenRate recoveryRate)
    (_hCycle : 0 < n) :
    let debt :=
      SleepDebtWeightedSchedule.iteratedDebt
        n cycleLength scheduledWake wakeBurdenRate recoveryRate
    ∃ boundary : QueueBoundaryWitnessNat_SleepQuorumQueueMoonshots,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.arrivalRate = canonicalFailureBudgetFromDebt debt ∧
      boundary.serviceRate =
        quorumSize (canonicalReplicaCountFromDebt debt)
          (canonicalFailureBudgetFromDebt debt) := by
  intro debt
  refine ⟨{
    beta1 := 0
    capacity := 1
    arrivalRate := canonicalFailureBudgetFromDebt debt
    serviceRate :=
      quorumSize (canonicalReplicaCountFromDebt debt)
        (canonicalFailureBudgetFromDebt debt)
  }, rfl, rfl, rfl, rfl⟩

theorem positive_weighted_sleep_debt_can_coexist_with_nonmajority_quorum :
    ∃ cycleLength scheduledWake wakeBurdenRate recoveryRate n replicaCount failureBudget : Nat,
      SleepDebtWeightedSchedule.thresholdRhs cycleLength recoveryRate <
          SleepDebtWeightedSchedule.thresholdLhs
            scheduledWake wakeBurdenRate recoveryRate ∧
      0 < n ∧
      0 < SleepDebtWeightedSchedule.iteratedDebt
            n cycleLength scheduledWake wakeBurdenRate recoveryRate ∧
      ¬ (2 * failureBudget < replicaCount) := by
  refine ⟨240, 210, 19, 101, 1, 2, 1, ?_⟩
  refine ⟨SleepDebtWeightedSchedule.literature_boundary_crossed_at_twentyone_hours,
    by decide, ?_, by decide⟩
  exact SleepDebtWeightedSchedule.iterated_debt_positive_above_threshold
    (cycleLength := 240)
    (scheduledWake := 210)
    (wakeBurdenRate := 19)
    (recoveryRate := 101)
    (n := 1)
    SleepDebtWeightedSchedule.literature_boundary_crossed_at_twentyone_hours
    (by decide)

structure GeometricErgodicityRateNat_SleepQuorumQueueMoonshots where
  numerator : Nat
  denominator : Nat
  initialBound : Nat
  hRateLtOne : numerator < denominator
  hDenomPos : 0 < denominator
  hInitialBoundPos : 0 < initialBound

def debtIndexedGeometricRate (debt : Nat) : GeometricErgodicityRateNat_SleepQuorumQueueMoonshots :=
  { numerator := 3
    denominator := 4
    initialBound := debt + 1
    hRateLtOne := by decide
    hDenomPos := by decide
    hInitialBoundPos := Nat.succ_pos _ }

theorem debtIndexedGeometricRate_contraction (debt : Nat) :
    (debtIndexedGeometricRate debt).numerator = 3 ∧
    (debtIndexedGeometricRate debt).denominator = 4 := by
  exact ⟨rfl, rfl⟩

theorem positive_weighted_sleep_debt_yields_geometric_rate_certificate
    {cycleLength scheduledWake wakeBurdenRate recoveryRate n : Nat}
    (hCrossed :
      SleepDebtWeightedSchedule.thresholdRhs cycleLength recoveryRate <
        SleepDebtWeightedSchedule.thresholdLhs
          scheduledWake wakeBurdenRate recoveryRate)
    (hCycle : 0 < n) :
    let debt :=
      SleepDebtWeightedSchedule.iteratedDebt
        n cycleLength scheduledWake wakeBurdenRate recoveryRate
    0 < debt ∧
    ∃ rate : GeometricErgodicityRateNat_SleepQuorumQueueMoonshots,
      rate = debtIndexedGeometricRate debt ∧
      rate.initialBound = debt + 1 ∧
      rate.numerator = 3 ∧
      rate.denominator = 4 := by
  intro debt
  have hDebtPos :
      0 < SleepDebtWeightedSchedule.iteratedDebt
            n cycleLength scheduledWake wakeBurdenRate recoveryRate :=
    SleepDebtWeightedSchedule.iterated_debt_positive_above_threshold hCrossed hCycle
  refine ⟨hDebtPos, debtIndexedGeometricRate debt, rfl, rfl, rfl, rfl⟩

structure MultiLevelHarrisWitnessNat_SleepQuorumQueueMoonshots where
  levels : Nat
  discreteDriftGap : Nat
  continuousDriftGap : Nat
  hDiscrete : 0 < discreteDriftGap
  hContinuous : 0 < continuousDriftGap

def debtIndexedMultiLevelHarrisWitness (debt : Nat) (hDebtPos : 0 < debt) :
    MultiLevelHarrisWitnessNat_SleepQuorumQueueMoonshots :=
  { levels := 2
    discreteDriftGap := debt
    continuousDriftGap := debt
    hDiscrete := hDebtPos
    hContinuous := hDebtPos }

theorem positive_weighted_sleep_debt_yields_multilevel_harris_witness
    {cycleLength scheduledWake wakeBurdenRate recoveryRate n : Nat}
    (hCrossed :
      SleepDebtWeightedSchedule.thresholdRhs cycleLength recoveryRate <
        SleepDebtWeightedSchedule.thresholdLhs
          scheduledWake wakeBurdenRate recoveryRate)
    (hCycle : 0 < n) :
    ∃ witness : MultiLevelHarrisWitnessNat_SleepQuorumQueueMoonshots,
      0 < witness.discreteDriftGap ∧
      0 < witness.continuousDriftGap := by
  have hDebtPos :
      0 < SleepDebtWeightedSchedule.iteratedDebt
            n cycleLength scheduledWake wakeBurdenRate recoveryRate :=
    SleepDebtWeightedSchedule.iterated_debt_positive_above_threshold hCrossed hCycle
  let witness :=
    debtIndexedMultiLevelHarrisWitness
      (SleepDebtWeightedSchedule.iteratedDebt
        n cycleLength scheduledWake wakeBurdenRate recoveryRate) hDebtPos
  exact ⟨witness, witness.hDiscrete, witness.hContinuous⟩

end Gnosis
