import Gnosis.PhyleLightEmission
import Gnosis.Electromagnetism
import Gnosis.PeruvianArchitectPrinciple

/-
  PhyleLightElectromagneticWitness.lean
  =====================================

  Connects the finite Phyle-light emission shape to the combinatorial
  electromagnetism surface. `PhyleLightEmission` proves the radial arithmetic:
  light ordinal `3`, Phyle carrier `9`, first-shell directions `27`, and
  three-shell emanation count `19683`. This module adds the first electrical
  content: a finite emitted shell with a nonzero electric flux.

  This still does not assert an empirical photon identity. It proves that the
  finite Phyle-light shell can carry a nonzero electric flux witness through
  `Gnosis.Electromagnetism`.
-/

namespace GnosisMath
namespace PhyleLightElectromagneticWitness

open Gnosis.VectorMath
open Gnosis.Electromagnetism
open Gnosis.SpectralNoiseEquilibrium
open GnosisMath.Phyle
open GnosisMath.PhyleLightEmission

/-- Unit vector used as both emitted electric field and outward normal. -/
def unitElectricVector : Vector3 where
  x := 1
  y := 0
  z := 0

/-- The finite shell point used for the minimal emitted surface witness. -/
def emittedShellPoint : BuleyUnit where
  waste := 1
  opportunity := 0
  diversity := 0

/--
  The first Keystone rung carrier. Its score has a visible `1` projection, but
  that number is only one face of the Bule carrier, not the carrier itself.
-/
def firstKeystoneRungBule : BuleyUnit :=
  emittedShellPoint

/-- Backward-compatible local name for the first nonzero carrier projection. -/
def plusOneBule : BuleyUnit :=
  firstKeystoneRungBule

/-- A one-point finite shell is the smallest closed carrier for a flux witness. -/
def emittedShellSurface : Surface where
  points := [emittedShellPoint]
  normals := fun _ => unitElectricVector
  is_closed := True

/-- The full first Phyle-light shell: one finite carrier point per emitted direction. -/
def fullRayShellSurface : Surface where
  points := List.replicate phyleLightDirectionCount emittedShellPoint
  normals := fun _ => unitElectricVector
  is_closed := True

/-- Constant emitted electric field on the finite shell. -/
def emittedElectricField : BuleyUnit → Vector3 :=
  fun _ => unitElectricVector

/-- Charge density matched to the emitted field dot outward normal. -/
def emittedChargeDensity : BuleyUnit → Int :=
  fun _ => 1

/-- The default three-shell emanation flux ledger: one unit per emitted ray. -/
def defaultEmanationFlux : Int :=
  Int.ofNat defaultEmanationRayCount

/-- The emitted field and shell normal have unit dot product. -/
theorem unit_electric_dot_closed :
    dot unitElectricVector unitElectricVector = 1 := by
  unfold dot unitElectricVector
  decide

/-- The first Keystone rung has exactly one unit of carrier score. -/
theorem first_keystone_rung_bule_score_closed :
    buleyUnitScore firstKeystoneRungBule = 1 := by
  unfold firstKeystoneRungBule emittedShellPoint buleyUnitScore
  decide

/-- The first Keystone rung is reached by past-side tension in the arch model. -/
theorem first_keystone_rung_lands_on_keystone :
    Gnosis.PeruvianArchitect.tension_force
      Gnosis.PeruvianArchitect.foundation_top =
      Gnosis.PeruvianArchitect.keystone :=
  Gnosis.PeruvianArchitect.foundation_to_keystone_tension

/-- Compatibility theorem: the old name has score one as a projection. -/
theorem plus_one_bule_score_closed :
    buleyUnitScore plusOneBule = 1 := by
  unfold plusOneBule
  exact first_keystone_rung_bule_score_closed

/-- The emitted charge density matches the field-normal dot product everywhere. -/
theorem emitted_charge_matches_flux_density
    (p : BuleyUnit) :
    emittedChargeDensity p =
      dot (emittedElectricField p) (emittedShellSurface.normals p) := by
  unfold emittedChargeDensity emittedElectricField emittedShellSurface
  exact unit_electric_dot_closed.symm

/-- The same unit density match holds across the full 27-direction shell. -/
theorem full_ray_shell_charge_matches_flux_density
    (p : BuleyUnit) :
    emittedChargeDensity p =
      dot (emittedElectricField p) (fullRayShellSurface.normals p) := by
  unfold emittedChargeDensity emittedElectricField fullRayShellSurface
  exact unit_electric_dot_closed.symm

/-- Closed arithmetic: the emitted shell has electric flux one. -/
theorem emitted_shell_flux_closed :
    boundary_integral_electric_flux emittedShellSurface emittedElectricField = 1 := by
  unfold boundary_integral_electric_flux emittedShellSurface emittedElectricField
    unitElectricVector dot
  decide

/-- The emitted shell has nonzero electric flux. -/
theorem emitted_shell_flux_nonzero :
    boundary_integral_electric_flux emittedShellSurface emittedElectricField ≠ 0 := by
  rw [emitted_shell_flux_closed]
  decide

/-- Closed arithmetic: the full first shell has electric flux twenty-seven. -/
theorem full_ray_shell_flux_closed :
    boundary_integral_electric_flux fullRayShellSurface emittedElectricField = 27 := by
  unfold boundary_integral_electric_flux fullRayShellSurface emittedElectricField
    phyleLightDirectionCount lightOrdinal unitElectricVector dot
  decide

/-- The full first shell has nonzero electric flux. -/
theorem full_ray_shell_flux_nonzero :
    boundary_integral_electric_flux fullRayShellSurface emittedElectricField ≠ 0 := by
  rw [full_ray_shell_flux_closed]
  decide

/-- Gauss-law bridge for the full 27-direction emitted shell. -/
theorem full_ray_shell_gauss_law :
    boundary_integral_electric_flux fullRayShellSurface emittedElectricField =
      total_enclosed_charge fullRayShellSurface emittedChargeDensity :=
  gauss_law_integral fullRayShellSurface emittedElectricField emittedChargeDensity
    True.intro full_ray_shell_charge_matches_flux_density

/-- Gauss-law bridge: the emitted shell flux equals its enclosed charge. -/
theorem emitted_shell_gauss_law :
    boundary_integral_electric_flux emittedShellSurface emittedElectricField =
      total_enclosed_charge emittedShellSurface emittedChargeDensity :=
  gauss_law_integral emittedShellSurface emittedElectricField emittedChargeDensity
    True.intro emitted_charge_matches_flux_density

/-- Closed arithmetic: the three-shell emanation flux ledger is 19,683. -/
theorem default_emanation_flux_closed :
    defaultEmanationFlux = 19683 := by
  unfold defaultEmanationFlux defaultEmanationRayCount emanationRayCount
    defaultEmanationShells phyleLightDirectionCount lightOrdinal phyleBars
  decide

/-- The three-shell emanation ledger has nonzero flux. -/
theorem default_emanation_flux_nonzero :
    defaultEmanationFlux ≠ 0 := by
  rw [default_emanation_flux_closed]
  decide

/--
  The electromagnetic Phyle-light bundle: the radial shape arithmetic survives,
  and the emitted shell carries a nonzero electric flux witnessed through
  `Gnosis.Electromagnetism`.
-/
theorem phyle_light_electromagnetic_bundle :
    lightOrdinal = 3 ∧
    phyleLightDirectionCount = 27 ∧
    defaultEmanationRayCount = 19683 ∧
    Gnosis.PeruvianArchitect.tension_force
      Gnosis.PeruvianArchitect.foundation_top =
      Gnosis.PeruvianArchitect.keystone ∧
    buleyUnitScore firstKeystoneRungBule = 1 ∧
    buleyUnitScore plusOneBule = 1 ∧
    boundary_integral_electric_flux emittedShellSurface emittedElectricField = 1 ∧
    boundary_integral_electric_flux emittedShellSurface emittedElectricField ≠ 0 ∧
    boundary_integral_electric_flux fullRayShellSurface emittedElectricField = 27 ∧
    boundary_integral_electric_flux fullRayShellSurface emittedElectricField ≠ 0 ∧
    defaultEmanationFlux = 19683 ∧
    defaultEmanationFlux ≠ 0 ∧
    boundary_integral_electric_flux emittedShellSurface emittedElectricField =
      total_enclosed_charge emittedShellSurface emittedChargeDensity ∧
    boundary_integral_electric_flux fullRayShellSurface emittedElectricField =
      total_enclosed_charge fullRayShellSurface emittedChargeDensity :=
  ⟨light_ordinal_closed, phyle_light_direction_count_closed,
   default_emanation_ray_count_closed, first_keystone_rung_lands_on_keystone,
   first_keystone_rung_bule_score_closed, plus_one_bule_score_closed, emitted_shell_flux_closed,
   emitted_shell_flux_nonzero, full_ray_shell_flux_closed,
   full_ray_shell_flux_nonzero, default_emanation_flux_closed,
   default_emanation_flux_nonzero, emitted_shell_gauss_law,
   full_ray_shell_gauss_law⟩

end PhyleLightElectromagneticWitness
end GnosisMath
