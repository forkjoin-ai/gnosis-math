import Gnosis.NoiseTopology
import Gnosis.ResolutionVsEvolution

namespace Gnosis

/-!
# Layered Noise Formalization

This module sharpens the existing `ResolutionVsEvolution` thesis into an
observer-relative model:

- a higher layer emits a finite structured signal,
- a lower observer has bounded bandwidth and bounded stable rows,
- the unresolved residue is what the lower layer experiences as noise,
- increasing resolution converts perceived noise back into explicit structure.

The point is not that noise is "broken data". The point is that noise is
structured excess relative to a finite observer contract.
-/

namespace LayeredNoise

open Gnosis.Noise
open Gnosis.Resolution

/-- A finite observer frame: what can be symbolized and what can be stably held. -/
structure ObserverFrame where
  bandwidth : Nat
  stableRows : Nat
deriving DecidableEq, Repr

/-- A signal from a higher layer: complexity, color class, and a finite
saturation budget attached to that color. -/
structure HigherLayerSignal where
  complexity : Nat
  color : NoiseColor
  saturationWitness : Nat
  saturationMatches : saturation color = saturationWitness
deriving DecidableEq

/-- The part of the higher signal that cannot be stably held by the observer. -/
def unresolvedResidue (frame : ObserverFrame) (signal : HigherLayerSignal) : Nat :=
  signal.saturationWitness - frame.stableRows

/-- Coherent information fits inside the observer bandwidth. -/
def coherentAt (frame : ObserverFrame) (signal : HigherLayerSignal) : Prop :=
  signal.complexity ≤ frame.bandwidth

/-- Incoherent information is still structured, but it exceeds the local bandwidth. -/
def incoherentAt (frame : ObserverFrame) (signal : HigherLayerSignal) : Prop :=
  perceived_noise frame.bandwidth signal.complexity

/-- Raising the observer bandwidth turns local incoherence into coherence. -/
def resolvedBy (higherBandwidth : Nat) (signal : HigherLayerSignal) : Prop :=
  is_structure higherBandwidth signal.complexity

/-- A canonical Aeon-limited observer. -/
def aeonObserver : ObserverFrame :=
  { bandwidth := Gnosis.Circadian.aeon
    stableRows := Gnosis.Circadian.aeon }

/-- Pink saturation as a higher-layer signal. -/
def pinkSaturationSignal : HigherLayerSignal :=
  { complexity := saturation NoiseColor.Pink
    color := NoiseColor.Pink
    saturationWitness := saturation NoiseColor.Pink
    saturationMatches := rfl }

/-- White saturation as the substrate limit. -/
def whiteSaturationSignal : HigherLayerSignal :=
  { complexity := saturation NoiseColor.White
    color := NoiseColor.White
    saturationWitness := saturation NoiseColor.White
    saturationMatches := rfl }

/-- Brown saturation as the heavier host-layer drift. -/
def brownSaturationSignal : HigherLayerSignal :=
  { complexity := saturation NoiseColor.Brown
    color := NoiseColor.Brown
    saturationWitness := saturation NoiseColor.Brown
    saturationMatches := rfl }

/-- The unresolved residue is exactly the excess above stable rows. -/
theorem unresolved_residue_eq_excess (frame : ObserverFrame) (signal : HigherLayerSignal)
    (hRows : frame.stableRows ≤ signal.saturationWitness) :
    unresolvedResidue frame signal + frame.stableRows = signal.saturationWitness := by
  unfold unresolvedResidue
  exact Nat.sub_add_cancel hRows

/-- Observer-local incoherence is exactly the existing `perceived_noise` notion. -/
theorem incoherence_is_resolution_gap (frame : ObserverFrame) (signal : HigherLayerSignal) :
    incoherentAt frame signal ↔ signal.complexity > frame.bandwidth := by
  rfl

/-- Any locally noisy signal becomes coherent at its own complexity ceiling. -/
theorem every_local_noise_has_resolving_bandwidth
    (frame : ObserverFrame) (signal : HigherLayerSignal)
    (_hNoise : incoherentAt frame signal) :
    resolvedBy signal.complexity signal := by
  unfold resolvedBy is_structure
  exact Nat.le_refl signal.complexity

/-- White, pink, and brown form the `10 / 30 / 90` saturation ladder. -/
theorem canonical_saturation_ladder :
    saturation NoiseColor.White = 10 ∧
    saturation NoiseColor.Pink = 30 ∧
    saturation NoiseColor.Brown = 90 := by
  decide

/-- The Aeon observer sees pink saturation as `12 + 18`: twelve stable rows,
eighteen unresolved units. -/
theorem pink_overflows_aeon_by_eighteen :
    unresolvedResidue aeonObserver pinkSaturationSignal = 18 := by
  have h :
      saturation NoiseColor.Pink - Gnosis.Circadian.aeon = 18 := by
    rw [cmb_is_pink_resonance]
    decide
  unfold unresolvedResidue aeonObserver pinkSaturationSignal
  simpa using h

/-- Pink saturation is locally incoherent for the Aeon observer because `30 > 12`. -/
theorem pink_is_local_noise_at_aeon :
    incoherentAt aeonObserver pinkSaturationSignal := by
  unfold incoherentAt perceived_noise aeonObserver pinkSaturationSignal
  simp [galactic_min_alignment]
  decide

/-- At the pink saturation bandwidth itself, the same signal becomes coherent. -/
theorem pink_resolves_at_pink_bandwidth :
    resolvedBy (saturation NoiseColor.Pink) pinkSaturationSignal := by
  exact every_local_noise_has_resolving_bandwidth aeonObserver pinkSaturationSignal
    pink_is_local_noise_at_aeon

/-- Brown carries strictly more unresolved residue than pink at the same Aeon observer. -/
theorem brown_exceeds_pink_residue_at_aeon :
    unresolvedResidue aeonObserver pinkSaturationSignal <
      unresolvedResidue aeonObserver brownSaturationSignal := by
  unfold unresolvedResidue aeonObserver pinkSaturationSignal brownSaturationSignal
  decide

/-- Increasing stable rows cannot increase unresolved residue for a fixed signal. -/
theorem more_stable_rows_reduce_residue
    (signal : HigherLayerSignal) {r1 r2 : Nat}
    (hOrder : r1 ≤ r2)
    (_hCap : r2 ≤ signal.saturationWitness) :
    unresolvedResidue ⟨signal.complexity, r2⟩ signal ≤
      unresolvedResidue ⟨signal.complexity, r1⟩ signal := by
  unfold unresolvedResidue
  exact Nat.sub_le_sub_left hOrder signal.saturationWitness

/-- A simple topological reading: the noise neighborhood is the observer's
unresolved residue, not a loss of global structure. -/
theorem residue_is_nonnegative_neighborhood
    (frame : ObserverFrame) (signal : HigherLayerSignal) :
    0 ≤ unresolvedResidue frame signal := by
  exact Nat.zero_le _

end LayeredNoise
end Gnosis
