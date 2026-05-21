import Gnosis.BuleyKenomaCycleWitness

/-
  BuleyKenomaBasinPeriod.lean
  ===========================

  Burns down the next-exploration target from
  `BuleyKenomaCycleWitness`: every explicitly enumerated ULR-basin tail
  snapshot from `iterate 6..10 nashPolarizationTrap` has the kenoma
  bulk index, then closes the local tail by proving the same statement
  for every `n ≥ 6`.

  Imports `Gnosis.BuleyKenomaCycleWitness`. Zero `sorry`, zero new
  `axiom`.
-/

namespace BuleyKenomaBasinPeriod

open SkyrmsUltraLongRunEquilibrium
open BuleyErgodicClosure

theorem nash_trap_iterate_six_to_ten_reaches_ulr :
    iterate 6 nashPolarizationTrap = skyrmsUltraLongRunFixedPoint ∧
    iterate 7 nashPolarizationTrap = skyrmsUltraLongRunFixedPoint ∧
    iterate 8 nashPolarizationTrap = skyrmsUltraLongRunFixedPoint ∧
    iterate 9 nashPolarizationTrap = skyrmsUltraLongRunFixedPoint ∧
    iterate 10 nashPolarizationTrap = skyrmsUltraLongRunFixedPoint := by
  unfold iterate mutationStep nashPolarizationTrap skyrmsUltraLongRunFixedPoint
  native_decide

theorem nash_trap_iterate_six_to_ten_bulk_is_kenoma :
    bulkOf (iterate 6 nashPolarizationTrap) = 55 ∧
    bulkOf (iterate 7 nashPolarizationTrap) = 55 ∧
    bulkOf (iterate 8 nashPolarizationTrap) = 55 ∧
    bulkOf (iterate 9 nashPolarizationTrap) = 55 ∧
    bulkOf (iterate 10 nashPolarizationTrap) = 55 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [nash_trap_iterate_six_to_ten_reaches_ulr.1]
    exact bulk_of_skyrms_ulr_eq_fifty_five
  · rw [nash_trap_iterate_six_to_ten_reaches_ulr.2.1]
    exact bulk_of_skyrms_ulr_eq_fifty_five
  · rw [nash_trap_iterate_six_to_ten_reaches_ulr.2.2.1]
    exact bulk_of_skyrms_ulr_eq_fifty_five
  · rw [nash_trap_iterate_six_to_ten_reaches_ulr.2.2.2.1]
    exact bulk_of_skyrms_ulr_eq_fifty_five
  · rw [nash_trap_iterate_six_to_ten_reaches_ulr.2.2.2.2]
    exact bulk_of_skyrms_ulr_eq_fifty_five

theorem ulr_basin_tail_period_witness :
    (∀ n : Nat, n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 →
      bulkOf (iterate n nashPolarizationTrap) = 55) := by
  intro n h
  rcases h with h6 | h7 | h8 | h9 | h10
  · rw [h6]; exact nash_trap_iterate_six_to_ten_bulk_is_kenoma.1
  · rw [h7]; exact nash_trap_iterate_six_to_ten_bulk_is_kenoma.2.1
  · rw [h8]; exact nash_trap_iterate_six_to_ten_bulk_is_kenoma.2.2.1
  · rw [h9]; exact nash_trap_iterate_six_to_ten_bulk_is_kenoma.2.2.2.1
  · rw [h10]; exact nash_trap_iterate_six_to_ten_bulk_is_kenoma.2.2.2.2

theorem iterate_add (m n : Nat) (s : PolarizationState) :
    iterate (m + n) s = iterate n (iterate m s) := by
  induction m generalizing s with
  | zero =>
      rw [Nat.zero_add]
      unfold iterate
      rfl
  | succ m ih =>
      rw [Nat.succ_add]
      rw [show iterate (m + 1) s = iterate m (mutationStep s) by rfl]
      exact ih (mutationStep s)

theorem ulr_fixed_for_all_future_iterates (n : Nat) :
    iterate n skyrmsUltraLongRunFixedPoint =
      skyrmsUltraLongRunFixedPoint := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [iterate, skyrms_ulr_is_mutation_fixed_point]
      exact ih

theorem nash_trap_iterate_six_add_reaches_ulr (k : Nat) :
    iterate (6 + k) nashPolarizationTrap =
      skyrmsUltraLongRunFixedPoint := by
  rw [iterate_add 6 k nashPolarizationTrap]
  rw [nash_trap_iterate_six_to_ten_reaches_ulr.1]
  exact ulr_fixed_for_all_future_iterates k

theorem nash_trap_iterate_six_add_bulk_is_kenoma (k : Nat) :
    bulkOf (iterate (6 + k) nashPolarizationTrap) = 55 := by
  rw [nash_trap_iterate_six_add_reaches_ulr k]
  exact bulk_of_skyrms_ulr_eq_fifty_five

theorem ulr_basin_tail_all_steps_ge_six :
    ∀ n : Nat, 6 ≤ n →
      bulkOf (iterate n nashPolarizationTrap) = 55 := by
  intro n hn
  rcases Nat.exists_eq_add_of_le hn with ⟨k, hk⟩
  rw [hk]
  exact nash_trap_iterate_six_add_bulk_is_kenoma k

/-! ## Next exploration

The finite kenoma-basin tail is closed for all `n ≥ 6`: after the
sixth mutation step, the Nash trap has reached the ULR fixed point,
and every future iterate preserves the kenoma bulk index.
-/

end BuleyKenomaBasinPeriod
