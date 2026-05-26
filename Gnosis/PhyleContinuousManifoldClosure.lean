import Gnosis.PhyleFiniteSampleUniversality

/-
  PhyleContinuousManifoldClosure.lean
  ===================================

  Closure step for the "every shape from Phyle" claim.

  The honest continuum statement is resolution-indexed: a continuous 3D
  manifold contributes finite sampled covers at every requested resolution, and
  each finite cover is carried by the Phyle/time-bridge encoding. Exact
  continuum equality would require a heavier topology/limit stack; this file
  proves the finite-cover closure needed by the visualizer.
-/

namespace GnosisMath
namespace PhyleContinuousManifoldClosure

open GnosisMath.PhyleFiniteSampleUniversality
open GnosisMath.TimeBridgeBigBangEmanation
open GnosisMath.TimeBridgePresentCarrier

/-- A resolution index for finite covers of a continuous 3D target. -/
abbrev Resolution := Nat

/--
  A continuous 3D manifold, as used here, is any target that can provide a
  finite sampled cover at every positive resolution.
-/
structure Continuous3DManifold where
  sampleCover : Resolution → FiniteSampledShape
  positiveResolutionNonempty :
    ∀ resolution : Resolution, 0 < resolution → 0 < (sampleCover resolution).length

/-- Phyle encoding of a continuous target at one finite resolution. -/
def phyleEncodeManifoldAt
    (manifold : Continuous3DManifold) (resolution : Resolution) :
    List FoldedParticle :=
  phyleEncodeSampledShape (manifold.sampleCover resolution)

theorem phyle_manifold_encoding_preserves_cover_count
    (manifold : Continuous3DManifold) (resolution : Resolution) :
    (phyleEncodeManifoldAt manifold resolution).length =
      (manifold.sampleCover resolution).length := by
  unfold phyleEncodeManifoldAt
  exact phyle_encode_preserves_sample_count (manifold.sampleCover resolution)

theorem phyle_manifold_positive_resolution_nonempty
    (manifold : Continuous3DManifold) (resolution : Resolution)
    (hResolution : 0 < resolution) :
    0 < (phyleEncodeManifoldAt manifold resolution).length := by
  rw [phyle_manifold_encoding_preserves_cover_count]
  exact manifold.positiveResolutionNonempty resolution hResolution

theorem phyle_manifold_encoded_samples_stable
    (manifold : Continuous3DManifold) (resolution : Resolution)
    (particle : FoldedParticle)
    (h : particle ∈ phyleEncodeManifoldAt manifold resolution) :
    mathematicallyStable defaultStabilityCutoff particle := by
  unfold phyleEncodeManifoldAt at h
  exact phyle_encoded_samples_stable (manifold.sampleCover resolution) particle h

theorem phyle_manifold_encoded_samples_survive_to_bridge
    (manifold : Continuous3DManifold) (resolution : Resolution)
    (particle : FoldedParticle)
    (h : particle ∈ phyleEncodeManifoldAt manifold resolution) :
    survivorCarrier defaultStabilityCutoff particle =
      some (timeBridgePresent.entry, timeBridgePresent.exit) := by
  unfold phyleEncodeManifoldAt at h
  exact phyle_encoded_samples_survive_to_bridge
    (manifold.sampleCover resolution) particle h

/--
  Resolution-indexed closure theorem: every continuous 3D manifold that supplies
  finite covers at every positive resolution has a nonempty Phyle encoding at
  every positive resolution; the encoding preserves cover cardinality, all
  samples are stable, and all samples survive to the bridge carrier.
-/
theorem phyle_continuous_3d_manifold_closure
    (manifold : Continuous3DManifold) (resolution : Resolution)
    (hResolution : 0 < resolution) :
    0 < (phyleEncodeManifoldAt manifold resolution).length ∧
    (phyleEncodeManifoldAt manifold resolution).length =
      (manifold.sampleCover resolution).length ∧
    (∀ particle ∈ phyleEncodeManifoldAt manifold resolution,
      mathematicallyStable defaultStabilityCutoff particle) ∧
    (∀ particle ∈ phyleEncodeManifoldAt manifold resolution,
      survivorCarrier defaultStabilityCutoff particle =
        some (timeBridgePresent.entry, timeBridgePresent.exit)) :=
  ⟨phyle_manifold_positive_resolution_nonempty manifold resolution hResolution,
   phyle_manifold_encoding_preserves_cover_count manifold resolution,
   phyle_manifold_encoded_samples_stable manifold resolution,
   phyle_manifold_encoded_samples_survive_to_bridge manifold resolution⟩

end PhyleContinuousManifoldClosure
end GnosisMath
