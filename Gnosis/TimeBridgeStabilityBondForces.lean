import Gnosis.TimeBridgeParticleShapeIsomorphism
import Gnosis.TimeBridgePhysicsStandingWaves

/-
  TimeBridgeStabilityBondForces.lean
  ==================================

  Formal support for jump scene 0: stability creates pairwise bonds. In this
  finite model, the bound pair uses the strong-force/fork projection, and the
  below-threshold/decaying case uses the weak-force/race projection.
-/

namespace GnosisMath
namespace TimeBridgeStabilityBondForces

open Gnosis.SpectralNoiseEquilibrium
open ForkRaceFoldVentAreForces
open GnosisMath.TimeBridgePresentCarrier
open GnosisMath.TimeBridgeBigBangEmanation
open GnosisMath.TimeBridgeParticleShapeIsomorphism
open GnosisMath.TimeBridgePhysicsStandingWaves

/-- A candidate pairwise bond between two folded particles. -/
structure StabilityBond where
  left : FoldedParticle
  right : FoldedParticle
  threshold : StabilityScore

/-- A bond is active when both particles pass the same stability threshold. -/
def pairwiseStable (bond : StabilityBond) : Prop :=
  mathematicallyStable bond.threshold bond.left ∧
  mathematicallyStable bond.threshold bond.right

/-- The stable bond shape is the named `bonds` particle presentation. -/
def stabilityBondCarrier :=
  shapeCarrier ParticleShape.bonds

/-- Concrete stable bond used by the visual default. -/
def firstStableBond : StabilityBond where
  left := stableParticleForShape ParticleShape.bonds
  right := stableParticleForShape ParticleShape.bonds
  threshold := defaultStabilityCutoff

theorem first_stable_bond_pairwise_stable :
    pairwiseStable firstStableBond := by
  constructor <;>
    exact stable_shape_particle_is_stable ParticleShape.bonds

/-- Pairwise stable bonds use the strong-force projection: a nontrivial bound carrier. -/
theorem pairwise_stability_projects_strong_force
    (bond : StabilityBond) (_h : pairwiseStable bond) :
    (fork_operator timeBridgePresent.firstUnit).length > 1 ∧
      ∃ total : Nat, total = buleyUnitScore timeBridgePresent.firstUnit :=
  time_bridge_strong_force_projection

/-- A failed pairwise bond decays through the weak-force projection. -/
theorem pairwise_instability_projects_weak_force
    (bond : StabilityBond) (_h : ¬ pairwiseStable bond) :
    buleyUnitScore (race_operator timeBridgePresent.firstUnit) ≤
      buleyUnitScore timeBridgePresent.firstUnit ∧
      ∃ n : Nat, n = buleyUnitScore timeBridgePresent.firstUnit :=
  time_bridge_weak_force_projection

/-- The stability-bond carrier is still the time-bridge carrier up to isomorphism. -/
theorem stability_bond_carrier_isomorphic_to_bridge :
    CarrierIsomorphic stabilityBondCarrier
      (timeBridgePresent.entry, timeBridgePresent.exit) := by
  unfold stabilityBondCarrier
  exact bonds_maps_to_bridge_carrier

/--
  Stability-bond force bundle: pairwise stable particles bind by the strong
  projection, unstable pairs decay by the weak projection, and the bond carrier
  remains isomorphic to the time bridge.
-/
theorem time_bridge_stability_bond_force_bundle :
    pairwiseStable firstStableBond ∧
    ((fork_operator timeBridgePresent.firstUnit).length > 1 ∧
      ∃ total : Nat, total = buleyUnitScore timeBridgePresent.firstUnit) ∧
    (∀ bond : StabilityBond, ¬ pairwiseStable bond →
      buleyUnitScore (race_operator timeBridgePresent.firstUnit) ≤
        buleyUnitScore timeBridgePresent.firstUnit ∧
        ∃ n : Nat, n = buleyUnitScore timeBridgePresent.firstUnit) ∧
    CarrierIsomorphic stabilityBondCarrier
      (timeBridgePresent.entry, timeBridgePresent.exit) :=
  ⟨first_stable_bond_pairwise_stable,
   pairwise_stability_projects_strong_force firstStableBond
    first_stable_bond_pairwise_stable,
   pairwise_instability_projects_weak_force,
   stability_bond_carrier_isomorphic_to_bridge⟩

end TimeBridgeStabilityBondForces
end GnosisMath
