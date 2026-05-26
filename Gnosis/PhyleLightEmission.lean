import Gnosis.Phyle
import Gnosis.LetThereBeVacuum

/-
  PhyleLightEmission.lean
  =======================

  Formalizes the wild visual target before rendering it: a finite radial Phyle
  emission shape. One source emits in many discrete directions; the direction
  count comes from the light ordinal (`3`) refracted through the Phyle carrier
  (`9`), giving `27` finite rays.

  This module intentionally proves a shape witness for light-emission geometry,
  not an empirical identity claim about photons. The stronger physical claim
  must pass through `Gnosis.Electromagnetism`.

  Init-only surface: closed arithmetic uses `decide`; structural equalities use
  `rfl`; no Mathlib, no `omega`.
-/

namespace GnosisMath
namespace PhyleLightEmission

open GnosisMath.Phyle

/-- The source point of a discrete radial emission. -/
structure SourcePoint where
  seed : Nat

/-- A finite direction emitted from a source. -/
abbrev Direction (n : Nat) := Fin n

/-- A finite ray is a source plus one discrete direction. -/
structure RadialRay (directions : Nat) where
  source : SourcePoint
  direction : Direction directions

/-- Light's ordinal from `LetThereBeVacuum`: three swerves from the void. -/
def lightOrdinal : Nat :=
  Gnosis.LetThereBeVacuum.CreationStep.Light.ordinal

/-- The Phyle refraction count: light ordinal through the nine-bar carrier. -/
def phyleLightDirectionCount : Nat :=
  lightOrdinal * phyleBars

/-- A concrete source used by the visual and later physics witnesses. -/
def originSource : SourcePoint where
  seed := 0

/-- The default finite Phyle-light ray type. -/
abbrev PhyleLightRay := RadialRay phyleLightDirectionCount

/-- Closed arithmetic: light is the third ordinal. -/
theorem light_ordinal_closed :
    lightOrdinal = 3 :=
  Gnosis.LetThereBeVacuum.light_is_third

/-- Closed arithmetic: the Phyle carrier has nine bars. -/
theorem phyle_light_carrier_closed :
    phyleBars = 9 :=
  phyle_is_tripod_of_tripods

/-- Closed arithmetic: Phyle-light emits along twenty-seven finite directions. -/
theorem phyle_light_direction_count_closed :
    phyleLightDirectionCount = 27 := by
  unfold phyleLightDirectionCount lightOrdinal phyleBars
  decide

/-- The finite radial emission has at least one direction, so a ray can exist. -/
theorem phyle_light_has_direction :
    0 < phyleLightDirectionCount := by
  unfold phyleLightDirectionCount lightOrdinal phyleBars
  decide

/-- The first concrete Phyle-light ray starts at the origin source. -/
def firstPhyleLightRay : PhyleLightRay where
  source := originSource
  direction := ⟨0, phyle_light_has_direction⟩

/-- A finite emanation address: a ray choice inside one radial shell. -/
structure EmanationStep (directions : Nat) where
  ray : Direction directions

/-- Race phase rotates a finite direction index without changing the carrier. -/
def racePhaseDirection {directions : Nat} (h : 0 < directions)
    (phase : Nat) (direction : Direction directions) : Direction directions :=
  ⟨(direction.val + phase) % directions, Nat.mod_lt _ h⟩

/-- Rays on rays on rays: repeated Phyle-light branching over finite shells. -/
def emanationRayCount (shells : Nat) : Nat :=
  phyleLightDirectionCount ^ shells

/-- The visual/default emanation depth: three shells, matching the light ordinal. -/
def defaultEmanationShells : Nat :=
  lightOrdinal

/-- The default emanation count: twenty-seven rays, three shells deep. -/
def defaultEmanationRayCount : Nat :=
  emanationRayCount defaultEmanationShells

/-- Every finite direction can be read as a ray from the same source. -/
def rayFromOrigin (direction : Direction phyleLightDirectionCount) : PhyleLightRay where
  source := originSource
  direction := direction

/-- Origin emission preserves the source for every emitted direction. -/
theorem ray_from_origin_preserves_source
    (direction : Direction phyleLightDirectionCount) :
    (rayFromOrigin direction).source = originSource :=
  rfl

/-- Race phase preserves the finite Phyle-light direction carrier. -/
theorem race_phase_preserves_direction_count
    (phase : Nat) (direction : Direction phyleLightDirectionCount) :
    (racePhaseDirection phyle_light_has_direction phase direction).val <
      phyleLightDirectionCount :=
  (racePhaseDirection phyle_light_has_direction phase direction).isLt

/-- Race phase moves direction addresses but keeps rays rooted at the source. -/
theorem race_phase_ray_preserves_source
    (phase : Nat) (direction : Direction phyleLightDirectionCount) :
    (rayFromOrigin
      (racePhaseDirection phyle_light_has_direction phase direction)).source =
      originSource :=
  rfl

/-- Zero race phase leaves a direction unchanged. -/
theorem race_phase_zero
    (direction : Direction phyleLightDirectionCount) :
    racePhaseDirection phyle_light_has_direction 0 direction = direction := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt direction.isLt

/-- Zero shells leave the source unresolved as one root. -/
theorem emanation_zero_shells :
    emanationRayCount 0 = 1 := by
  unfold emanationRayCount
  decide

/-- One shell is exactly the finite Phyle-light direction count. -/
theorem emanation_one_shell :
    emanationRayCount 1 = phyleLightDirectionCount := by
  unfold emanationRayCount
  decide

/-- Closed arithmetic: the default emanation has three shells. -/
theorem default_emanation_shells_closed :
    defaultEmanationShells = 3 :=
  light_ordinal_closed

/-- Closed arithmetic: rays on rays on rays produce 19,683 finite rays. -/
theorem default_emanation_ray_count_closed :
    defaultEmanationRayCount = 19683 := by
  unfold defaultEmanationRayCount emanationRayCount defaultEmanationShells
    phyleLightDirectionCount lightOrdinal phyleBars
  decide

/-- Emanation is nonempty at the default three-shell depth. -/
theorem default_emanation_nonempty :
    0 < defaultEmanationRayCount := by
  unfold defaultEmanationRayCount emanationRayCount defaultEmanationShells
    phyleLightDirectionCount lightOrdinal phyleBars
  decide

/--
  The finite Phyle-light bundle: light sits at ordinal three, the Phyle carrier
  has nine bars, their discrete refraction gives twenty-seven directions, and
  every direction is rooted at the same source. Repeating the ray rule for
  three shells gives the finite emanation count.
-/
theorem phyle_light_emission_bundle :
    lightOrdinal = 3 ∧
    phyleBars = 9 ∧
    phyleLightDirectionCount = 27 ∧
    0 < phyleLightDirectionCount ∧
    defaultEmanationShells = 3 ∧
    defaultEmanationRayCount = 19683 ∧
    0 < defaultEmanationRayCount ∧
    (∀ direction : Direction phyleLightDirectionCount,
      (rayFromOrigin direction).source = originSource) ∧
    (∀ phase : Nat, ∀ direction : Direction phyleLightDirectionCount,
      (rayFromOrigin
        (racePhaseDirection phyle_light_has_direction phase direction)).source =
        originSource) :=
  ⟨light_ordinal_closed, phyle_light_carrier_closed,
   phyle_light_direction_count_closed, phyle_light_has_direction,
   default_emanation_shells_closed, default_emanation_ray_count_closed,
   default_emanation_nonempty, ray_from_origin_preserves_source,
   race_phase_ray_preserves_source⟩

end PhyleLightEmission
end GnosisMath
