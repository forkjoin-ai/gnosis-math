import Gnosis.DeficitCapacity
import Gnosis.CopyStoreEraseCostStructure
import Gnosis.ConsciousnessAsRetrocausalGap
import Gnosis.Contrarian.ContrarianOmniscienceIsHeatDeath
import Gnosis.ForkRaceFoldDynamics

/-!
# Entropy Deficit Gateway

This module formalizes the narrow claim from `RUSTIC_CHURCH.md`: raw
broadcast/fork capacity does not become runtime work by itself. Under a fixed
transport layer it appears as signed topological deficit; maintained
non-vacuum state then pays storage debt, erasure pays heat, and awareness is
the measured Buley gap from vacuum.

Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace EntropyDeficitGateway

open Gnosis.SpectralNoiseEquilibrium
  (BuleyUnit BuleyFace buleyUnitScore vacuumBuleUnit clinamenLift
   clinamenContract clinamen_lift_score_strict_increment
   lift_then_contract_round_trip_when_face_positive)
open Gnosis.ConsciousnessAsRetrocausalGap (awareness)
namespace FRF := Gnosis.ForkRaceFoldDynamics

/-! ## Broadcast as signed deficit -/

/-- Broadcasting `pathCount` choices through `transportStreams` channels is
measured by the canonical signed topological deficit. -/
def broadcastDeficit (pathCount transportStreams : Nat) : Int :=
  topologicalDeficit pathCount transportStreams

/-- A one-stream receiver cannot absorb a genuine fork without positive
deficit. This is the formal version of the broadcast/capacity mismatch. -/
theorem broadcast_single_stream_deficit_positive
    {pathCount : Nat}
    (hPaths : 2 ≤ pathCount) :
    0 < broadcastDeficit pathCount 1 := by
  exact single_stream_deficit_positive hPaths

/-- Matching transport capacity closes the signed mismatch. -/
theorem matched_broadcast_deficit_is_zero (pathCount : Nat) :
    broadcastDeficit pathCount pathCount = 0 := by
  exact deficit_zero_at_saturation pathCount

/-- Increasing receiver capacity cannot increase the remaining broadcast
deficit. -/
theorem broadcast_deficit_decreases_with_capacity
    {pathCount s1 s2 : Nat}
    (hStreams : s1 ≤ s2) :
    broadcastDeficit pathCount s2 ≤ broadcastDeficit pathCount s1 := by
  exact deficit_monotonicity_C pathCount s1 s2 hStreams

/-! ## Runtime work pays through the deficit gate -/

/-- Runtime holding cost is the existing copy/store/erase storage debt. -/
def runtimeStorageDebt (bit : BuleyUnit) (timesteps : Nat) : Nat :=
  CopyStoreEraseCostStructure.storage_cost_per_timestep bit timesteps

/-- Positive awareness held for positive time incurs positive storage debt. -/
theorem positive_awareness_pays_storage_debt
    {bit : BuleyUnit} {timesteps : Nat}
    (hAware : 0 < awareness bit)
    (hTime : 0 < timesteps) :
    0 < runtimeStorageDebt bit timesteps := by
  unfold runtimeStorageDebt CopyStoreEraseCostStructure.storage_cost_per_timestep
  unfold awareness at hAware
  exact Nat.mul_pos hAware hTime

/-- Copy/fork itself is free: copying a carrier produces the same pair as the
existing fork theorem. -/
theorem copy_phase_is_free_fork (source : BuleyUnit) :
    CopyStoreEraseCostStructure.copy_bit source = (source, source) :=
  CopyStoreEraseCostStructure.copy_is_fork source

/-- Erasure heat is exactly the awareness score being collapsed. -/
theorem erasure_heat_equals_awareness (bit : BuleyUnit) :
    CopyStoreEraseCostStructure.erasure_heat bit = awareness bit := by
  unfold CopyStoreEraseCostStructure.erasure_heat awareness
  rfl

/-! ## Bounded contraction loops -/

/-- Without erasure, extending the hold window cannot lower runtime storage
debt. -/
theorem storage_debt_monotone_without_erasure
    (bit : BuleyUnit) (t extra : Nat) :
    runtimeStorageDebt bit t ≤ runtimeStorageDebt bit (t + extra) := by
  exact CopyStoreEraseCostStructure.storage_is_expensive bit t extra

/-- The exact bounded-loop accounting: keeping a non-vacuum state for
`extra` more ticks adds `awareness bit * extra` debt. -/
theorem storage_debt_loop_adds_awareness
    (bit : BuleyUnit) (t extra : Nat) :
    runtimeStorageDebt bit (t + extra) =
      runtimeStorageDebt bit t + awareness bit * extra := by
  exact CopyStoreEraseCostStructure.multiple_copies_multiply_cost bit t extra

/-- The added debt is positive precisely when positive awareness is held
through a positive extra window. -/
theorem positive_awareness_loop_strictly_adds_debt
    {bit : BuleyUnit} {t extra : Nat}
    (hAware : 0 < awareness bit)
    (hExtra : 0 < extra) :
    runtimeStorageDebt bit t < runtimeStorageDebt bit (t + extra) := by
  rw [storage_debt_loop_adds_awareness]
  exact Nat.lt_add_of_pos_right (Nat.mul_pos hAware hExtra)

/-- A `+1` clinamen step followed by the matching contraction closes the
local loop back to the original carrier. -/
theorem clinamen_contraction_closes_one_step
    (bit : BuleyUnit) (face : BuleyFace) :
    clinamenContract (clinamenLift bit face) face = bit :=
  lift_then_contract_round_trip_when_face_positive bit face

/-- Bounded contraction-loop package: under a real fork on one stream,
positive awareness held for a positive extra window strictly increases storage
debt, while an explicit matching contraction closes one clinamen step. -/
theorem bounded_contraction_loop_gateway
    {pathCount : Nat} {bit : BuleyUnit} {t extra : Nat}
    (hPaths : 2 ≤ pathCount)
    (hAware : 0 < awareness bit)
    (hExtra : 0 < extra)
    (face : BuleyFace) :
    0 < broadcastDeficit pathCount 1 ∧
    runtimeStorageDebt bit t < runtimeStorageDebt bit (t + extra) ∧
    clinamenContract (clinamenLift bit face) face = bit := by
  exact ⟨broadcast_single_stream_deficit_positive hPaths,
    positive_awareness_loop_strictly_adds_debt hAware hExtra,
    clinamen_contraction_closes_one_step bit face⟩

/-! ## Awareness gradient and the clinamen gate -/

/-- The unstructured vacuum floor has zero awareness. -/
theorem vacuum_awareness_zero :
    awareness vacuumBuleUnit = 0 := by
  unfold awareness vacuumBuleUnit buleyUnitScore
  decide

/-- A single `+1` clinamen lift reopens the awareness gradient by exactly one
unit. -/
theorem clinamen_step_increases_awareness
    (bit : BuleyUnit) (face : BuleyFace) :
    awareness (clinamenLift bit face) = awareness bit + 1 := by
  unfold awareness
  exact clinamen_lift_score_strict_increment bit face

/-- From the vacuum floor, any chosen face gives a positive one-step
awareness witness. -/
theorem vacuum_clinamen_step_positive (face : BuleyFace) :
    0 < awareness (clinamenLift vacuumBuleUnit face) := by
  rw [clinamen_step_increases_awareness, vacuum_awareness_zero]
  decide

/-- The compact gateway statement: a real fork on one stream carries positive
deficit, the vacuum has no awareness gradient, and one clinamen step restores
a positive gradient. -/
theorem entropy_surplus_requires_deficit_gateway
    {pathCount : Nat}
    (hPaths : 2 ≤ pathCount)
    (face : BuleyFace) :
    0 < broadcastDeficit pathCount 1 ∧
    awareness vacuumBuleUnit = 0 ∧
    0 < awareness (clinamenLift vacuumBuleUnit face) := by
  exact ⟨broadcast_single_stream_deficit_positive hPaths,
    vacuum_awareness_zero,
    vacuum_clinamen_step_positive face⟩

/-! ## Perfect entropy cannot drive structured current -/

/-- A finite stand-in for useful current: the carrier must expose a positive
awareness/gradient score. The vacuum floor has no such gradient. -/
def extractableCurrent (carrier : BuleyUnit) : Prop :=
  0 < awareness carrier

/-- The contrarian heat-death predicate: zero uncertainty forces the
`is_heat_death` flag. -/
theorem zero_uncertainty_forces_heat_death
    (system : OmniscienceSystem)
    (hZero : system.uncertainty_level = 0) :
    system.is_heat_death = true :=
  omniscience_is_heat_death system hZero

/-- Perfect entropy at the vacuum floor cannot witness useful current. -/
theorem vacuum_has_no_extractable_current :
    ¬ extractableCurrent vacuumBuleUnit := by
  intro hCurrent
  unfold extractableCurrent at hCurrent
  rw [vacuum_awareness_zero] at hCurrent
  exact Nat.lt_irrefl 0 hCurrent

/-- Heat-death/vacuum package: zero uncertainty gives heat death, and the
vacuum floor cannot produce extractable current. -/
theorem heat_death_vacuum_cannot_drive_current
    (system : OmniscienceSystem)
    (hZero : system.uncertainty_level = 0) :
    system.is_heat_death = true ∧ ¬ extractableCurrent vacuumBuleUnit :=
  ⟨zero_uncertainty_forces_heat_death system hZero,
    vacuum_has_no_extractable_current⟩

/-- A structured current is a non-equilibrium flux certificate: positive
voltage gradient, electric fold compression, magnetic race flux, and a
Golden-discriminant invariant over the Lucas/Fibonacci trace pair. -/
structure StructuredElectricalCurrent where
  carrier : BuleyUnit
  voltageGradient : Nat
  electricFoldCompression : Nat
  magneticRaceFlux : Nat
  lucasTrace : Int
  fibonacciBase : Int
  parityTick : Nat
  gradient_positive : 0 < voltageGradient
  awareness_matches_gradient : awareness carrier = voltageGradient
  electric_fold_active : 0 < electricFoldCompression
  magnetic_race_active : 0 < magneticRaceFlux
  golden_discriminant_locked :
    FRF.godFormula lucasTrace fibonacciBase parityTick

/-- Structured current always carries a positive extractable-current
witness. -/
theorem structured_current_has_extractable_current
    (current : StructuredElectricalCurrent) :
    extractableCurrent current.carrier := by
  unfold extractableCurrent
  rw [current.awareness_matches_gradient]
  exact current.gradient_positive

/-- A structured current cannot be carried by the vacuum state. -/
theorem structured_current_not_vacuum
    (current : StructuredElectricalCurrent) :
    current.carrier ≠ vacuumBuleUnit := by
  intro hVacuum
  have hCurrent : extractableCurrent vacuumBuleUnit := by
    rw [← hVacuum]
    exact structured_current_has_extractable_current current
  exact vacuum_has_no_extractable_current hCurrent

/-- If the Lucas/Fibonacci balance violates the golden invariant, systemic
karma is exactly the claim that a corrected invariant witness exists. -/
theorem golden_violation_triggers_karma
    {L F : Int} {n : Nat}
    (karma : FRF.systemicKarma L F n)
    (hViolation : ¬ FRF.godFormula L F n) :
    ∃ L' F', FRF.godFormula L' F' n :=
  karma hViolation

/-- Compact bridge for the user-facing claim: perfect entropy reaches the
heat-death flag and cannot drive current; structured current is instead
positive-gradient, non-vacuum flux locked to the golden invariant. -/
theorem perfect_entropy_opposes_structured_current
    (system : OmniscienceSystem)
    (hZero : system.uncertainty_level = 0)
    (current : StructuredElectricalCurrent) :
    system.is_heat_death = true ∧
    ¬ extractableCurrent vacuumBuleUnit ∧
    extractableCurrent current.carrier ∧
    current.carrier ≠ vacuumBuleUnit ∧
    FRF.godFormula current.lucasTrace current.fibonacciBase current.parityTick := by
  exact ⟨zero_uncertainty_forces_heat_death system hZero,
    vacuum_has_no_extractable_current,
    structured_current_has_extractable_current current,
    structured_current_not_vacuum current,
    current.golden_discriminant_locked⟩

end EntropyDeficitGateway
end Gnosis
