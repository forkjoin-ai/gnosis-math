import Gnosis.KnowledgeVoidComplement
import Gnosis.TimeBridgeGnosisClock

/-
  NoiseSpectrumResolution.lean
  ============================

  Formalizes the new noise-spectrum reading: unresolved noise is remaining
  void; resolved color/knowledge is the conserved complement; the resolution
  reset is periodic on the twelve-phase Gnosis clock.
-/

namespace Gnosis
namespace NoiseSpectrumResolution

open Gnosis.EntropyOfTheVoid
open Gnosis.KnowledgeVoidComplement
open Gnosis.GnosisTimeClock
open Gnosis.AeonCycleTwelveShadow

/-- A finite noise-spectrum state read through the void/knowledge ledger. -/
structure NoiseSpectrumState where
  voidState : VoidState
  phase : TimePhase
  targetPhase : TimePhase

/-- A spectrum is resolved in phase when observation phase matches target phase. -/
def inResolutionPhase (N : NoiseSpectrumState) : Prop :=
  N.phase = N.targetPhase

/-- Signal read at the wrong phase appears as noise. -/
def wrongPhaseNoise (N : NoiseSpectrumState) : Prop :=
  N.phase ≠ N.targetPhase

instance inResolutionPhaseDecidable (N : NoiseSpectrumState) :
    Decidable (inResolutionPhase N) :=
  inferInstanceAs (Decidable (N.phase = N.targetPhase))

/-- Remaining void entropy is the unresolved base before phase alignment. -/
def unresolved_base_perthou (N : NoiseSpectrumState) : Nat :=
  void_entropy_perthou N.voidState

/-- Resolved spectral color is the knowledge complement. -/
def resolved_color_perthou (N : NoiseSpectrumState) : Nat :=
  knowledge_perthou N.voidState

/-- Noise is not chaotic unfolding: it is signal not yet resolved in phase. -/
def unresolved_noise_perthou (N : NoiseSpectrumState) : Nat :=
  if inResolutionPhase N then
    unresolved_base_perthou N
  else
    void_knowledge_total_perthou N.voidState

/-- One Gnosis-clock step of spectral resolution time. -/
def noiseTick (N : NoiseSpectrumState) : NoiseSpectrumState :=
  { N with phase := tick N.phase }

/-- The post-session spectrum at present phase. -/
def postSessionNoiseSpectrum : NoiseSpectrumState :=
  { voidState := post_session_void
    phase := phaseOfNatTick 0
    targetPhase := phaseOfNatTick 0 }

/-- The same ledger sampled one Gnosis tick out of phase. -/
def postSessionWrongPhaseSpectrum : NoiseSpectrumState :=
  { voidState := post_session_void
    phase := phaseOfNatTick 1
    targetPhase := phaseOfNatTick 0 }

theorem post_session_spectrum_in_phase :
    inResolutionPhase postSessionNoiseSpectrum := by
  rfl

theorem post_session_wrong_phase_is_noise :
    wrongPhaseNoise postSessionWrongPhaseSpectrum := by
  unfold wrongPhaseNoise postSessionWrongPhaseSpectrum
  decide

theorem in_phase_noise_equals_base
    (N : NoiseSpectrumState) (hPhase : inResolutionPhase N) :
    unresolved_noise_perthou N = unresolved_base_perthou N := by
  unfold unresolved_noise_perthou
  rw [if_pos hPhase]

theorem wrong_phase_noise_equals_total
    (N : NoiseSpectrumState) (hPhase : wrongPhaseNoise N) :
    unresolved_noise_perthou N =
      void_knowledge_total_perthou N.voidState := by
  unfold unresolved_noise_perthou
  apply if_neg
  exact hPhase

/-- The resolved color is the complement of unresolved noise. -/
theorem resolved_color_is_noise_complement
    (N : NoiseSpectrumState)
    (h : N.voidState.bits_resolved_by_measurement ≤
      log2_void N.voidState.total_possibility_count) :
    void_knowledge_total_perthou N.voidState -
      unresolved_base_perthou N =
        resolved_color_perthou N := by
  unfold unresolved_base_perthou resolved_color_perthou
  exact knowledge_is_one_minus_void N.voidState h

/-- Twelve Gnosis-clock ticks preserve the noise-spectrum phase. -/
theorem noise_resolution_periodic_twelve (N : NoiseSpectrumState) :
    tickIterate twelve N.phase = N.phase :=
  tickIterate_twelve N.phase

/-- The post-session spectrum resolves to 8000 color / 2000 noise. -/
theorem post_session_noise_color_resolution_closed :
    resolved_color_perthou postSessionNoiseSpectrum = 8000 ∧
    unresolved_noise_perthou postSessionNoiseSpectrum = 2000 := by
  constructor
  · decide
  · rw [in_phase_noise_equals_base postSessionNoiseSpectrum post_session_spectrum_in_phase]
    decide

theorem post_session_wrong_phase_noise_closed :
    unresolved_noise_perthou postSessionWrongPhaseSpectrum = 10000 := by
  rw [wrong_phase_noise_equals_total postSessionWrongPhaseSpectrum post_session_wrong_phase_is_noise]
  decide

/--
  Noise-spectrum resolution bundle: spectral noise and color are complement
  ledgers, and the reset periodicity is the twelve-phase Gnosis clock.
-/
theorem noise_spectrum_resolution_bundle :
    resolved_color_perthou postSessionNoiseSpectrum = 8000 ∧
    unresolved_noise_perthou postSessionNoiseSpectrum = 2000 ∧
    unresolved_noise_perthou postSessionWrongPhaseSpectrum = 10000 ∧
    inResolutionPhase postSessionNoiseSpectrum ∧
    wrongPhaseNoise postSessionWrongPhaseSpectrum ∧
    void_knowledge_total_perthou postSessionNoiseSpectrum.voidState -
      unresolved_base_perthou postSessionNoiseSpectrum =
        resolved_color_perthou postSessionNoiseSpectrum ∧
    tickIterate twelve postSessionNoiseSpectrum.phase =
      postSessionNoiseSpectrum.phase :=
  ⟨post_session_noise_color_resolution_closed.1,
   post_session_noise_color_resolution_closed.2,
   post_session_wrong_phase_noise_closed,
   post_session_spectrum_in_phase,
   post_session_wrong_phase_is_noise,
   resolved_color_is_noise_complement postSessionNoiseSpectrum (by decide),
   noise_resolution_periodic_twelve postSessionNoiseSpectrum⟩

end NoiseSpectrumResolution
end Gnosis
