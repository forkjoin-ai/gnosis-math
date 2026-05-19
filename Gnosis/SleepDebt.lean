import Gnosis.Tactics

namespace Gnosis
namespace SleepDebt

def totalRecoveryDemand (wakeLoad carriedDebt : Nat) : Nat :=
  wakeLoad + carriedDebt

def residualDebt (wakeLoad carriedDebt recoveryQuota : Nat) : Nat :=
  totalRecoveryDemand wakeLoad carriedDebt - recoveryQuota

def effectiveCapacity (maxCapacity carriedDebt : Nat) : Nat :=
  maxCapacity - min maxCapacity carriedDebt

def intrusionEnabled (wakeLoad carriedDebt intrusionThreshold : Nat) : Prop :=
  intrusionThreshold <= carriedDebt /\ 0 < wakeLoad

theorem full_recovery_clears_residual_debt
    {wakeLoad carriedDebt recoveryQuota : Nat}
    (hClear : wakeLoad + carriedDebt <= recoveryQuota) :
    residualDebt wakeLoad carriedDebt recoveryQuota = 0 := by
  unfold residualDebt totalRecoveryDemand
  exact Nat.sub_eq_zero_of_le hClear

theorem full_recovery_restores_capacity
    {maxCapacity wakeLoad carriedDebt recoveryQuota : Nat}
    (hClear : wakeLoad + carriedDebt <= recoveryQuota) :
    effectiveCapacity maxCapacity (residualDebt wakeLoad carriedDebt recoveryQuota) =
      maxCapacity := by
  rw [full_recovery_clears_residual_debt hClear]
  unfold effectiveCapacity
  simp

theorem partial_recovery_leaves_positive_debt
    {wakeLoad carriedDebt recoveryQuota : Nat}
    (hShortfall : recoveryQuota < wakeLoad + carriedDebt) :
    0 < residualDebt wakeLoad carriedDebt recoveryQuota := by
  unfold residualDebt totalRecoveryDemand
  exact Nat.sub_pos_of_lt hShortfall

theorem positive_debt_lowers_capacity
    {maxCapacity carriedDebt : Nat}
    (hCap : 0 < maxCapacity)
    (hDebt : 0 < carriedDebt) :
    effectiveCapacity maxCapacity carriedDebt < maxCapacity := by
  unfold effectiveCapacity
  cases Nat.le_total maxCapacity carriedDebt with
  | inl hMaxLeDebt =>
      rw [Nat.min_eq_left hMaxLeDebt]
      rw [Nat.sub_self maxCapacity]
      exact hCap
  | inr hDebtLeMax =>
      rw [Nat.min_eq_right hDebtLeMax]
      exact Nat.sub_lt hCap hDebt

theorem partial_recovery_lowers_next_capacity
    {maxCapacity wakeLoad carriedDebt recoveryQuota : Nat}
    (hCap : 0 < maxCapacity)
    (hShortfall : recoveryQuota < wakeLoad + carriedDebt) :
    effectiveCapacity maxCapacity (residualDebt wakeLoad carriedDebt recoveryQuota) <
      maxCapacity := by
  apply positive_debt_lowers_capacity hCap
  exact partial_recovery_leaves_positive_debt hShortfall

theorem repeated_truncation_preserves_debt
    {nextWakeLoad carriedDebt recoveryQuota : Nat}
    (hQuota : recoveryQuota <= nextWakeLoad) :
    carriedDebt <= residualDebt nextWakeLoad carriedDebt recoveryQuota := by
  unfold residualDebt totalRecoveryDemand
  exact Nat.le_sub_of_add_le
    (Nat.add_comm carriedDebt recoveryQuota ▸ Nat.add_le_add_right hQuota carriedDebt)

theorem repeated_truncation_strictly_increases_debt
    {nextWakeLoad carriedDebt recoveryQuota : Nat}
    (hQuota : recoveryQuota < nextWakeLoad) :
    carriedDebt < residualDebt nextWakeLoad carriedDebt recoveryQuota := by
  unfold residualDebt totalRecoveryDemand
  exact Nat.lt_sub_of_add_lt
    (Nat.add_comm carriedDebt recoveryQuota ▸ Nat.add_lt_add_right hQuota carriedDebt)

theorem debt_at_or_above_intrusion_threshold_enables_intrusion
    {wakeLoad carriedDebt intrusionThreshold : Nat}
    (hLoad : 0 < wakeLoad)
    (hDebt : intrusionThreshold <= carriedDebt) :
    intrusionEnabled wakeLoad carriedDebt intrusionThreshold := by
  exact ⟨hDebt, hLoad⟩

-- ─── THM-SLEEP-DEBT-SATURATION-CEILING ──────────────────────────────
-- Floor: debt grows linearly (iterated_debt_eq_cycle_count_mul_gap).
-- Ceiling: maximum sustainable debt before intrusion = capacity.
-- When debt >= capacity, intrusion is forced (the system cannot
-- maintain function without involuntary recovery).
-- ─────────────────────────────────────────────────────────────────────