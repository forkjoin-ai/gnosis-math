import Gnosis.BuleyErgodicClosure

/-
  BuleyKenomaCycleWitness.lean
  ============================

  Burns down the next-exploration target from `BuleyErgodicClosure`:
  after ten forward mutation steps from the Nash trap, the bulk index
  has reached the same kenoma value as the Skyrms ULR fixed point.

  Imports `Gnosis.BuleyErgodicClosure`. Zero `sorry`, zero new `axiom`.
-/

namespace BuleyKenomaCycleWitness

open SkyrmsUltraLongRunEquilibrium
open BuleyErgodicClosure

theorem nash_trap_ten_steps_reaches_ulr :
    iterate 10 nashPolarizationTrap = skyrmsUltraLongRunFixedPoint := by
  unfold iterate mutationStep nashPolarizationTrap skyrmsUltraLongRunFixedPoint
  rfl

theorem nash_trap_ten_step_bulk_is_kenoma :
    bulkOf (iterate 10 nashPolarizationTrap) = 55 := by
  rw [nash_trap_ten_steps_reaches_ulr]
  exact bulk_of_skyrms_ulr_eq_fifty_five

theorem nash_trap_ten_step_bulk_matches_ulr :
    bulkOf (iterate 10 nashPolarizationTrap) =
      bulkOf skyrmsUltraLongRunFixedPoint := by
  rw [nash_trap_ten_steps_reaches_ulr]

theorem ten_step_kenoma_cycle_witness :
    bulkOf (iterate 10 nashPolarizationTrap) =
      bulkOf skyrmsUltraLongRunFixedPoint ∧
    bulkOf skyrmsUltraLongRunFixedPoint = 55 := by
  exact ⟨nash_trap_ten_step_bulk_matches_ulr,
    bulk_of_skyrms_ulr_eq_fifty_five⟩

/-! ## Next exploration

Closed by `Gnosis.BuleyKenomaBasinPeriod`: the explicitly enumerated
ULR-basin snapshots now share the finite tail bulk witness.
-/

end BuleyKenomaCycleWitness
