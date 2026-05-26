import Gnosis.TimeBridgeGnosisClock
import Gnosis.PhyleLightElectromagneticWitness

/-
  TimeBridgeBigBangEmanation.lean
  =================================

  Formal support for the hotkey-4 visual:

  * a single source emits a finite Phyle-light cloud,
  * each particle carries a stability score and a Gnosis-clock phase,
  * particles below the cutoff decay from the bridge carrier,
  * stable folded particles occupy the same two-port carrier and can form the
    visible bridge structure.

  This is a finite discrete witness for the visualization. It does not assert
  an empirical cosmology claim.
-/

namespace GnosisMath
namespace TimeBridgeBigBangEmanation

open GnosisMath.PhyleLightEmission
open GnosisMath.PhyleLightElectromagneticWitness
open Gnosis.Electromagnetism
open GnosisMath.CalatravaBridge
open GnosisMath.TimeBridgePresentCarrier
open GnosisMath.TimeBridgeTritonDynamics
open GnosisMath.TimeBridgeGnosisClock

/-- A stability score for a folded emitted particle. -/
abbrev StabilityScore := Nat

/-- The default stability cutoff used by the visual/theory bridge. -/
def defaultStabilityCutoff : StabilityScore :=
  phyleLightDirectionCount

/-- A particle emitted from the first source into the finite Phyle-light shell. -/
structure FoldedParticle where
  ray : PhyleLightRay
  clockPhase : TemporalDynamic
  stability : StabilityScore

/-- A particle survives exactly when its score reaches the cutoff. -/
def mathematicallyStable (cutoff : StabilityScore) (particle : FoldedParticle) : Prop :=
  cutoff ≤ particle.stability

instance stableDecidable (cutoff : StabilityScore) (particle : FoldedParticle) :
    Decidable (mathematicallyStable cutoff particle) :=
  inferInstanceAs (Decidable (cutoff ≤ particle.stability))

/--
  Stable particles fold onto the bridge carrier. Unstable particles decay from
  the carrier surface instead of adding load-bearing structure.
-/
def survivorCarrier (cutoff : StabilityScore) (particle : FoldedParticle) :
    Option (PathologicTwoPort × PathologicTwoPort) :=
  if mathematicallyStable cutoff particle then
    some (dynamicCarrier particle.clockPhase)
  else
    none

/-- The surviving particle carrier and the bridge carrier use the same two ports. -/
def CarrierIsomorphic
    (left right : PathologicTwoPort × PathologicTwoPort) : Prop :=
  left = right

/-- The finite cloud size used by the big-bang emanation mode. -/
def bigBangCloudSize : Nat :=
  defaultEmanationRayCount

/-- A concrete stable particle at the source. -/
def firstStableParticle : FoldedParticle where
  ray := firstPhyleLightRay
  clockPhase := TemporalDynamic.presentDefer
  stability := defaultStabilityCutoff

/-- A concrete decaying particle at the source. -/
def firstDecayingParticle : FoldedParticle where
  ray := firstPhyleLightRay
  clockPhase := TemporalDynamic.presentDefer
  stability := 0

/-- Re-root a particle at any finite source seed without changing its direction. -/
def particleFromSource (source : SourcePoint)
    (direction : Direction phyleLightDirectionCount)
    (phase : TemporalDynamic)
    (stability : StabilityScore) : FoldedParticle where
  ray := { source := source, direction := direction }
  clockPhase := phase
  stability := stability

theorem default_stability_cutoff_closed :
    defaultStabilityCutoff = 27 :=
  phyle_light_direction_count_closed

theorem big_bang_cloud_size_closed :
    bigBangCloudSize = 19683 :=
  default_emanation_ray_count_closed

theorem first_stable_particle_is_stable :
    mathematicallyStable defaultStabilityCutoff firstStableParticle := by
  unfold mathematicallyStable firstStableParticle
  exact Nat.le_refl defaultStabilityCutoff

theorem first_decaying_particle_is_not_stable :
    ¬ mathematicallyStable defaultStabilityCutoff firstDecayingParticle := by
  unfold mathematicallyStable firstDecayingParticle defaultStabilityCutoff
    phyleLightDirectionCount lightOrdinal GnosisMath.Phyle.phyleBars
  decide

/-- A stable particle occupies the same two-port bridge carrier. -/
theorem stable_particle_folds_onto_bridge
    (cutoff : StabilityScore) (particle : FoldedParticle)
    (hStable : mathematicallyStable cutoff particle) :
    survivorCarrier cutoff particle =
      some (timeBridgePresent.entry, timeBridgePresent.exit) := by
  unfold survivorCarrier
  simp [hStable, dynamicCarrier]

/-- A decaying particle does not contribute to the bridge carrier. -/
theorem unstable_particle_decays
    (cutoff : StabilityScore) (particle : FoldedParticle)
    (hUnstable : ¬ mathematicallyStable cutoff particle) :
    survivorCarrier cutoff particle = none := by
  unfold survivorCarrier
  simp [hUnstable]

/-- The first stable particle lands on the present bridge carrier. -/
theorem first_stable_particle_folds_onto_bridge :
    survivorCarrier defaultStabilityCutoff firstStableParticle =
      some (timeBridgePresent.entry, timeBridgePresent.exit) :=
  stable_particle_folds_onto_bridge defaultStabilityCutoff firstStableParticle
    first_stable_particle_is_stable

/-- The first decaying particle fades out before it can form structure. -/
theorem first_decaying_particle_decays :
    survivorCarrier defaultStabilityCutoff firstDecayingParticle = none :=
  unstable_particle_decays defaultStabilityCutoff firstDecayingParticle
    first_decaying_particle_is_not_stable

/-- Stable particles rooted at the source preserve source and carrier simultaneously. -/
theorem stable_particle_preserves_source_and_carrier
    (cutoff : StabilityScore) (particle : FoldedParticle)
    (hSource : particle.ray.source = originSource)
    (hStable : mathematicallyStable cutoff particle) :
    particle.ray.source = originSource ∧
    survivorCarrier cutoff particle =
      some (timeBridgePresent.entry, timeBridgePresent.exit) := by
  constructor
  · exact hSource
  · exact stable_particle_folds_onto_bridge cutoff particle hStable

/-- Clock phase changes do not alter the carrier reached by a stable particle. -/
theorem stable_particle_clock_phase_preserves_carrier
    (cutoff : StabilityScore) (particle : FoldedParticle)
    (phase : TemporalDynamic)
    (hStable : mathematicallyStable cutoff particle) :
    survivorCarrier cutoff { particle with clockPhase := phase } =
      survivorCarrier cutoff particle := by
  rw [stable_particle_folds_onto_bridge cutoff { particle with clockPhase := phase } hStable,
      stable_particle_folds_onto_bridge cutoff particle hStable]

/-- In the survivor case, the final particle carrier is isomorphic to the bridge carrier. -/
theorem stable_particle_carrier_isomorphic_to_bridge
    (cutoff : StabilityScore) (particle : FoldedParticle)
    (_hStable : mathematicallyStable cutoff particle) :
    CarrierIsomorphic (dynamicCarrier particle.clockPhase)
      (timeBridgePresent.entry, timeBridgePresent.exit) := by
  unfold CarrierIsomorphic dynamicCarrier
  rfl

/--
  The source seed can move arbitrarily: once the folded particle passes the
  stability cutoff, its survivor carrier is still the same time-bridge carrier.
-/
theorem stable_particle_from_any_source_folds_onto_bridge
    (source : SourcePoint)
    (direction : Direction phyleLightDirectionCount)
    (phase : TemporalDynamic)
    (cutoff stability : StabilityScore)
    (hStable : cutoff ≤ stability) :
    survivorCarrier cutoff
      (particleFromSource source direction phase stability) =
        some (timeBridgePresent.entry, timeBridgePresent.exit) := by
  exact stable_particle_folds_onto_bridge cutoff
    (particleFromSource source direction phase stability) hStable

/-- Any source seed has the same survivor-carrier isomorphism after stabilization. -/
theorem any_source_survivor_carrier_isomorphic
    (source : SourcePoint)
    (direction : Direction phyleLightDirectionCount)
    (phase : TemporalDynamic)
    (cutoff stability : StabilityScore)
    (hStable : cutoff ≤ stability) :
    CarrierIsomorphic
      (dynamicCarrier
        (particleFromSource source direction phase stability).clockPhase)
      (timeBridgePresent.entry, timeBridgePresent.exit) :=
  stable_particle_carrier_isomorphic_to_bridge cutoff
    (particleFromSource source direction phase stability) hStable

/--
  Big-bang emanation bundle: the source emits the finite default Phyle-light
  cloud, stable folded particles land on the two-port time bridge, unstable
  particles decay, and Gnosis-clock phase changes preserve the carrier topology.
-/
theorem time_bridge_big_bang_emanation_bundle :
    bigBangCloudSize = 19683 ∧
    defaultStabilityCutoff = 27 ∧
    boundary_integral_electric_flux fullRayShellSurface emittedElectricField = 27 ∧
    survivorCarrier defaultStabilityCutoff firstStableParticle =
      some (timeBridgePresent.entry, timeBridgePresent.exit) ∧
    survivorCarrier defaultStabilityCutoff firstDecayingParticle = none ∧
    (∀ cutoff : StabilityScore, ∀ particle : FoldedParticle,
      mathematicallyStable cutoff particle →
        survivorCarrier cutoff particle =
          some (timeBridgePresent.entry, timeBridgePresent.exit)) ∧
    (∀ cutoff : StabilityScore, ∀ particle : FoldedParticle,
      ¬ mathematicallyStable cutoff particle →
        survivorCarrier cutoff particle = none) ∧
    (∀ cutoff : StabilityScore, ∀ particle : FoldedParticle,
      mathematicallyStable cutoff particle →
        CarrierIsomorphic (dynamicCarrier particle.clockPhase)
          (timeBridgePresent.entry, timeBridgePresent.exit)) ∧
    (∀ source : SourcePoint,
      survivorCarrier defaultStabilityCutoff
        (particleFromSource source
          firstPhyleLightRay.direction TemporalDynamic.presentDefer
          defaultStabilityCutoff) =
        some (timeBridgePresent.entry, timeBridgePresent.exit)) :=
  ⟨big_bang_cloud_size_closed, default_stability_cutoff_closed,
   full_ray_shell_flux_closed, first_stable_particle_folds_onto_bridge,
   first_decaying_particle_decays, stable_particle_folds_onto_bridge,
   unstable_particle_decays, stable_particle_carrier_isomorphic_to_bridge,
   fun source =>
    stable_particle_from_any_source_folds_onto_bridge source
      firstPhyleLightRay.direction TemporalDynamic.presentDefer
      defaultStabilityCutoff defaultStabilityCutoff
      (Nat.le_refl defaultStabilityCutoff)⟩

end TimeBridgeBigBangEmanation
end GnosisMath
