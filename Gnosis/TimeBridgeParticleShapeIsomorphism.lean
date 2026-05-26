import Gnosis.TimeBridgeBigBangEmanation

/-
  TimeBridgeParticleShapeIsomorphism.lean
  =======================================

  Formalizes the non-bridge particle fields used by the visualizer. Sphere,
  helix, torus, lattice, and wave are alternate finite presentations of the
  same survivor carrier: after the stability cutoff, each maps back to the
  two-port time bridge up to the named carrier isomorphism.
-/

namespace GnosisMath
namespace TimeBridgeParticleShapeIsomorphism

open GnosisMath.PhyleLightEmission
open GnosisMath.CalatravaBridge
open GnosisMath.TimeBridgePresentCarrier
open GnosisMath.TimeBridgeTritonDynamics
open GnosisMath.TimeBridgeBigBangEmanation

/-- Particle target families exposed by the time-bridge visualizer. -/
inductive ParticleShape
  | bridge
  | sphere
  | helix
  | torus
  | lattice
  | wave
  | dna
  | bonds
  | stringTubes
  | monsterJewel
  deriving DecidableEq, Repr

/-- The non-bridge particle shapes are all alternate presentations. -/
def nonBridgeShape : ParticleShape → Prop
  | .bridge => False
  | .sphere => True
  | .helix => True
  | .torus => True
  | .lattice => True
  | .wave => True
  | .dna => True
  | .bonds => True
  | .stringTubes => True
  | .monsterJewel => True

/-- Every particle shape is read through a temporal phase before stabilization. -/
def particleShapePhase : ParticleShape → TemporalDynamic
  | .bridge => TemporalDynamic.presentDefer
  | .sphere => TemporalDynamic.futureCommit
  | .helix => TemporalDynamic.presentDefer
  | .torus => TemporalDynamic.pastCollapse
  | .lattice => TemporalDynamic.presentDefer
  | .wave => TemporalDynamic.futureCommit
  | .dna => TemporalDynamic.presentDefer
  | .bonds => TemporalDynamic.presentDefer
  | .stringTubes => TemporalDynamic.futureCommit
  | .monsterJewel => TemporalDynamic.futureCommit

/-- A stable particle emitted through a named shape family. -/
def stableParticleForShape (shape : ParticleShape) : FoldedParticle :=
  particleFromSource originSource firstPhyleLightRay.direction
    (particleShapePhase shape) defaultStabilityCutoff

/-- Shape presentations all use the same bridge carrier after stabilization. -/
def shapeCarrier (shape : ParticleShape) : PathologicTwoPort × PathologicTwoPort :=
  dynamicCarrier (particleShapePhase shape)

theorem stable_shape_particle_is_stable (shape : ParticleShape) :
    mathematicallyStable defaultStabilityCutoff (stableParticleForShape shape) := by
  unfold stableParticleForShape particleFromSource mathematicallyStable
  exact Nat.le_refl defaultStabilityCutoff

theorem shape_carrier_isomorphic_to_bridge (shape : ParticleShape) :
    CarrierIsomorphic (shapeCarrier shape)
      (timeBridgePresent.entry, timeBridgePresent.exit) := by
  unfold CarrierIsomorphic shapeCarrier dynamicCarrier
  rfl

theorem stable_shape_survives_to_bridge (shape : ParticleShape) :
    survivorCarrier defaultStabilityCutoff (stableParticleForShape shape) =
      some (timeBridgePresent.entry, timeBridgePresent.exit) :=
  stable_particle_folds_onto_bridge defaultStabilityCutoff
    (stableParticleForShape shape) (stable_shape_particle_is_stable shape)

/-- Sphere particle fields map back to the time-bridge carrier. -/
theorem sphere_maps_to_bridge_carrier :
    CarrierIsomorphic (shapeCarrier ParticleShape.sphere)
      (timeBridgePresent.entry, timeBridgePresent.exit) :=
  shape_carrier_isomorphic_to_bridge ParticleShape.sphere

/-- Helix particle fields map back to the time-bridge carrier. -/
theorem helix_maps_to_bridge_carrier :
    CarrierIsomorphic (shapeCarrier ParticleShape.helix)
      (timeBridgePresent.entry, timeBridgePresent.exit) :=
  shape_carrier_isomorphic_to_bridge ParticleShape.helix

/-- Torus particle fields map back to the time-bridge carrier. -/
theorem torus_maps_to_bridge_carrier :
    CarrierIsomorphic (shapeCarrier ParticleShape.torus)
      (timeBridgePresent.entry, timeBridgePresent.exit) :=
  shape_carrier_isomorphic_to_bridge ParticleShape.torus

/-- Lattice particle fields map back to the time-bridge carrier. -/
theorem lattice_maps_to_bridge_carrier :
    CarrierIsomorphic (shapeCarrier ParticleShape.lattice)
      (timeBridgePresent.entry, timeBridgePresent.exit) :=
  shape_carrier_isomorphic_to_bridge ParticleShape.lattice

/-- Wave particle fields map back to the time-bridge carrier. -/
theorem wave_maps_to_bridge_carrier :
    CarrierIsomorphic (shapeCarrier ParticleShape.wave)
      (timeBridgePresent.entry, timeBridgePresent.exit) :=
  shape_carrier_isomorphic_to_bridge ParticleShape.wave

/-- DNA-scale Phyle helix fields map back to the time-bridge carrier. -/
theorem dna_maps_to_bridge_carrier :
    CarrierIsomorphic (shapeCarrier ParticleShape.dna)
      (timeBridgePresent.entry, timeBridgePresent.exit) :=
  shape_carrier_isomorphic_to_bridge ParticleShape.dna

/-- Stability-bond particle fields map back to the time-bridge carrier. -/
theorem bonds_maps_to_bridge_carrier :
    CarrierIsomorphic (shapeCarrier ParticleShape.bonds)
      (timeBridgePresent.entry, timeBridgePresent.exit) :=
  shape_carrier_isomorphic_to_bridge ParticleShape.bonds

/-- String-thread tube particle fields map back to the time-bridge carrier. -/
theorem string_tubes_maps_to_bridge_carrier :
    CarrierIsomorphic (shapeCarrier ParticleShape.stringTubes)
      (timeBridgePresent.entry, timeBridgePresent.exit) :=
  shape_carrier_isomorphic_to_bridge ParticleShape.stringTubes

/-- Monster-jewel particle fields map back to the time-bridge carrier. -/
theorem monster_jewel_maps_to_bridge_carrier :
    CarrierIsomorphic (shapeCarrier ParticleShape.monsterJewel)
      (timeBridgePresent.entry, timeBridgePresent.exit) :=
  shape_carrier_isomorphic_to_bridge ParticleShape.monsterJewel

/--
  Ergodicity witness for this finite presentation surface: every named particle
  target family can be generated from the Phyle bridge carrier in the sense
  that its carrier is isomorphic to the bridge carrier.
-/
theorem phyle_shape_ergodicity_witness :
    ∀ shape : ParticleShape,
      CarrierIsomorphic (shapeCarrier shape)
        (timeBridgePresent.entry, timeBridgePresent.exit) :=
  shape_carrier_isomorphic_to_bridge

/--
  Particle-shape isomorphism bundle: every non-bridge shape exposed by the
  visualizer has a stable particle presentation that survives to the same
  two-port bridge carrier.
-/
theorem time_bridge_particle_shape_isomorphism_bundle :
    (∀ shape : ParticleShape,
      nonBridgeShape shape →
        CarrierIsomorphic (shapeCarrier shape)
          (timeBridgePresent.entry, timeBridgePresent.exit)) ∧
    (∀ shape : ParticleShape,
      nonBridgeShape shape →
        survivorCarrier defaultStabilityCutoff (stableParticleForShape shape) =
          some (timeBridgePresent.entry, timeBridgePresent.exit)) ∧
    CarrierIsomorphic (shapeCarrier ParticleShape.sphere)
      (timeBridgePresent.entry, timeBridgePresent.exit) ∧
    CarrierIsomorphic (shapeCarrier ParticleShape.helix)
      (timeBridgePresent.entry, timeBridgePresent.exit) ∧
    CarrierIsomorphic (shapeCarrier ParticleShape.torus)
      (timeBridgePresent.entry, timeBridgePresent.exit) ∧
    CarrierIsomorphic (shapeCarrier ParticleShape.lattice)
      (timeBridgePresent.entry, timeBridgePresent.exit) ∧
    CarrierIsomorphic (shapeCarrier ParticleShape.wave)
      (timeBridgePresent.entry, timeBridgePresent.exit) ∧
    CarrierIsomorphic (shapeCarrier ParticleShape.dna)
      (timeBridgePresent.entry, timeBridgePresent.exit) ∧
    CarrierIsomorphic (shapeCarrier ParticleShape.bonds)
      (timeBridgePresent.entry, timeBridgePresent.exit) ∧
    CarrierIsomorphic (shapeCarrier ParticleShape.stringTubes)
      (timeBridgePresent.entry, timeBridgePresent.exit) ∧
    CarrierIsomorphic (shapeCarrier ParticleShape.monsterJewel)
      (timeBridgePresent.entry, timeBridgePresent.exit) :=
  ⟨fun shape _ => shape_carrier_isomorphic_to_bridge shape,
   fun shape _ => stable_shape_survives_to_bridge shape,
   sphere_maps_to_bridge_carrier, helix_maps_to_bridge_carrier,
   torus_maps_to_bridge_carrier, lattice_maps_to_bridge_carrier,
   wave_maps_to_bridge_carrier, dna_maps_to_bridge_carrier,
   bonds_maps_to_bridge_carrier, string_tubes_maps_to_bridge_carrier,
   monster_jewel_maps_to_bridge_carrier⟩

end TimeBridgeParticleShapeIsomorphism
end GnosisMath
