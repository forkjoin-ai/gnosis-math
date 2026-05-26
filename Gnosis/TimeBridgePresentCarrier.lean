import Gnosis.CalatravaBridge
import Gnosis.PhyleLightEmission
import Gnosis.PhyleLightElectromagneticWitness
import Gnosis.TritonReintegration

/-
  TimeBridgePresentCarrier.lean
  =============================

  Formalizes the time-bridge reading:

  * past and future are the two reversible boundary ports,
  * present is the finite carrier that crosses between them,
  * race phase may move the embedding, but it does not break the topology,
  * the present carries the existing Triton middle (`abstain` / defer) and the
    Bule opportunity face, rather than reducing the Bule to its numeric `1`
    projection.

  This is a structural theorem about the finite carrier, not an empirical claim
  about spacetime measurement.
-/

namespace GnosisMath
namespace TimeBridgePresentCarrier

open GnosisMath.CalatravaBridge
open GnosisMath.PhyleLightEmission
open GnosisMath.PhyleLightElectromagneticWitness
open Gnosis.SpectralNoiseEquilibrium
open Gnosis.TritonCanonical

/-- The two temporal boundary names. -/
inductive TemporalBoundary
  | past
  | future
  deriving DecidableEq, Repr

/-- Map named temporal boundaries to the pathologic two-port carrier. -/
def temporalBoundaryPort : TemporalBoundary → PathologicTwoPort
  | .past => 0
  | .future => 1

/-- Present is the carrier between temporal boundary ports. -/
structure PresentCarrier where
  entry : PathologicTwoPort
  exit : PathologicTwoPort
  middle : Verdict
  firstUnit : BuleyUnit

/-- The canonical time bridge: past enters, future exits, present carries the Triton middle. -/
def timeBridgePresent : PresentCarrier where
  entry := temporalBoundaryPort .past
  exit := temporalBoundaryPort .future
  middle := Verdict.abstain
  firstUnit := plusOneBule

/-- Past is boundary port zero. -/
theorem past_boundary_closed :
    temporalBoundaryPort .past = (0 : PathologicTwoPort) :=
  rfl

/-- Future is boundary port one. -/
theorem future_boundary_closed :
    temporalBoundaryPort .future = (1 : PathologicTwoPort) :=
  rfl

/-- Present carries from past to future in one oriented two-port step. -/
theorem present_carries_past_to_future :
    orientedPortStep (by decide : 0 < 2) timeBridgePresent.entry =
      timeBridgePresent.exit := by
  unfold timeBridgePresent temporalBoundaryPort
  exact two_port_zero_steps_to_one

/-- The temporal bridge is reversible: future steps back to past. -/
theorem present_reverses_future_to_past :
    orientedPortStep (by decide : 0 < 2) timeBridgePresent.exit =
      timeBridgePresent.entry := by
  unfold timeBridgePresent temporalBoundaryPort
  exact two_port_one_steps_to_zero

/-- The present carrier's middle is the canonical Triton defer/abstain state. -/
theorem present_middle_is_triton_abstain :
    timeBridgePresent.middle = Verdict.abstain :=
  rfl

/-- The present carrier's middle has Triton sign zero. -/
theorem present_middle_sign_zero :
    sign timeBridgePresent.middle = 0 := by
  unfold timeBridgePresent
  exact sign_abstain

/-- The present carrier's Triton middle maps to the Bule opportunity face. -/
theorem present_middle_maps_to_bule_opportunity :
    Gnosis.TritonReintegration.verdictToBule timeBridgePresent.middle =
      ThreePhysicsForkRaceFoldBijection.BuleFace.Optimality := by
  unfold timeBridgePresent
  exact Gnosis.TritonReintegration.triton_middle_is_opportunity

/-- The present carrier's first Bule has score one as a projection. -/
theorem present_first_unit_score_projection :
    buleyUnitScore timeBridgePresent.firstUnit = 1 := by
  unfold timeBridgePresent
  exact plus_one_bule_score_closed

/-- Race phase preserves the present source of every Phyle-light ray. -/
theorem race_phase_preserves_present_source
    (phase : Nat) (direction : Direction phyleLightDirectionCount) :
    (rayFromOrigin
      (racePhaseDirection phyle_light_has_direction phase direction)).source =
      originSource :=
  race_phase_ray_preserves_source phase direction

/--
  Time bridge bundle: past and future are the two boundary holes, present is the
  carrier between them, the Triton middle is the defer/abstain state mapped to
  the Bule opportunity face, and race phase preserves the finite Phyle-light
  source while the embedding moves.
-/
theorem time_bridge_present_bundle :
    temporalBoundaryPort .past = (0 : PathologicTwoPort) ∧
    temporalBoundaryPort .future = (1 : PathologicTwoPort) ∧
    orientedPortStep (by decide : 0 < 2) timeBridgePresent.entry =
      timeBridgePresent.exit ∧
    orientedPortStep (by decide : 0 < 2) timeBridgePresent.exit =
      timeBridgePresent.entry ∧
    timeBridgePresent.middle = Verdict.abstain ∧
    sign timeBridgePresent.middle = 0 ∧
    Gnosis.TritonReintegration.verdictToBule timeBridgePresent.middle =
      ThreePhysicsForkRaceFoldBijection.BuleFace.Optimality ∧
    buleyUnitScore timeBridgePresent.firstUnit = 1 ∧
    phyleLightDirectionCount = 27 ∧
    defaultEmanationRayCount = 19683 ∧
    (∀ phase : Nat, ∀ direction : Direction phyleLightDirectionCount,
      (rayFromOrigin
        (racePhaseDirection phyle_light_has_direction phase direction)).source =
        originSource) :=
  ⟨past_boundary_closed, future_boundary_closed,
   present_carries_past_to_future, present_reverses_future_to_past,
   present_middle_is_triton_abstain, present_middle_sign_zero,
   present_middle_maps_to_bule_opportunity, present_first_unit_score_projection,
   phyle_light_direction_count_closed,
   default_emanation_ray_count_closed, race_phase_preserves_present_source⟩

end TimeBridgePresentCarrier
end GnosisMath
