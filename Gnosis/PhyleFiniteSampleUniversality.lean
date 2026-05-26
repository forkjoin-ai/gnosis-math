import Gnosis.TimeBridgeParticleShapeIsomorphism

/-
  PhyleFiniteSampleUniversality.lean
  ==================================

  Honest universality target for the visualizer: every finite sampled shape
  can be encoded as a finite list of Phyle-stable particles whose carrier maps
  back to the same time bridge. This is not yet a theorem about arbitrary
  continuous 3D manifolds; it is the finite sampling theorem needed before
  taking refinement limits.
-/

namespace GnosisMath
namespace PhyleFiniteSampleUniversality

open GnosisMath.TimeBridgeBigBangEmanation
open GnosisMath.TimeBridgeParticleShapeIsomorphism
open GnosisMath.TimeBridgePresentCarrier

/-- A discrete visual sample point, using integer-like natural coordinates. -/
structure SamplePoint where
  x : Nat
  y : Nat
  z : Nat
  deriving DecidableEq, Repr

/-- A finite sampled shape is a finite list of sample points. -/
abbrev FiniteSampledShape := List SamplePoint

/-- Encode each sample point as one stable Phyle particle presentation. -/
def phyleEncodeSampledShape (shape : FiniteSampledShape) : List FoldedParticle :=
  shape.map fun _ => stableParticleForShape ParticleShape.stringTubes

/-- The encoding preserves finite sample cardinality. -/
theorem phyle_encode_preserves_sample_count (shape : FiniteSampledShape) :
    (phyleEncodeSampledShape shape).length = shape.length := by
  unfold phyleEncodeSampledShape
  rw [List.length_map]

/-- Every encoded sample is mathematically stable. -/
theorem phyle_encoded_samples_stable
    (shape : FiniteSampledShape) (particle : FoldedParticle)
    (h : particle ∈ phyleEncodeSampledShape shape) :
    mathematicallyStable defaultStabilityCutoff particle := by
  unfold phyleEncodeSampledShape at h
  rcases List.mem_map.mp h with ⟨_sample, _hsample, hparticle⟩
  rw [← hparticle]
  exact stable_shape_particle_is_stable ParticleShape.stringTubes

/-- Every encoded stable sample lands on the same time-bridge carrier. -/
theorem phyle_encoded_samples_survive_to_bridge
    (shape : FiniteSampledShape) (particle : FoldedParticle)
    (h : particle ∈ phyleEncodeSampledShape shape) :
    survivorCarrier defaultStabilityCutoff particle =
      some (timeBridgePresent.entry, timeBridgePresent.exit) :=
  stable_particle_folds_onto_bridge defaultStabilityCutoff particle
    (phyle_encoded_samples_stable shape particle h)

/--
  Finite universality bundle: every finite sampled shape has a Phyle encoding
  with the same number of samples, all encoded samples are stable, and every
  encoded sample survives to the time-bridge carrier.
-/
theorem phyle_finite_sample_universality_bundle (shape : FiniteSampledShape) :
    (phyleEncodeSampledShape shape).length = shape.length ∧
    (∀ particle ∈ phyleEncodeSampledShape shape,
      mathematicallyStable defaultStabilityCutoff particle) ∧
    (∀ particle ∈ phyleEncodeSampledShape shape,
      survivorCarrier defaultStabilityCutoff particle =
        some (timeBridgePresent.entry, timeBridgePresent.exit)) :=
  ⟨phyle_encode_preserves_sample_count shape,
   phyle_encoded_samples_stable shape,
   phyle_encoded_samples_survive_to_bridge shape⟩

end PhyleFiniteSampleUniversality
end GnosisMath
