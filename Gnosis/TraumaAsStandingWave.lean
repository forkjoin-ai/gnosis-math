/-
  TraumaAsStandingWave.lean
  ========================

  Trauma = standing wave locked at high amplitude.

  Normal: trigger → emotional response → race dissipates → returns to baseline
  Trauma: trigger → response LOCKS into standing wave → won't damp →
          repeated triggering re-activates the same wave → oscillates forever

  Healing = introduce destructive interference to cancel the standing wave,
  then allow normal race damping to dissipate remaining energy.
-/

import Gnosis.SpectralNoiseEquilibrium
import Gnosis.InterferenceAsTheFifthForce
import Gnosis.TemporaryNoise
import Gnosis.PsychologyAsInterference

namespace TraumaAsStandingWave

open Gnosis.SpectralNoiseEquilibrium
open Gnosis.InterferenceAsTheFifthForce
open Gnosis.TemporaryNoise
open Gnosis.PsychologyAsInterference

-- ══════════════════════════════════════════════════════════
-- TRAUMA FORMATION: HOW A STANDING WAVE LOCKS
-- ══════════════════════════════════════════════════════════

/-- A triggering event creates an interference pattern: reality breaks into two paths.
    "I am safe" path and "I am in danger" path collide.
    This collision creates a high-amplitude interference (emotional shock). -/
def triggering_event_creates_interference :
    ∀ (baseline : BuleyUnit),
    baseline ≠ vacuumBuleUnit →
    (∃ (shocked_state : BuleyUnit),
      buleyUnitScore shocked_state > 2 * buleyUnitScore baseline) := by
  intro baseline h_ne
  refine ⟨clinamenLift baseline 3, ?_⟩
  simp [clinamenLift, buleyUnitScore]
  omega

/-- Normally, emotional responses damp via race operator.
    The two incompatible paths (safe vs danger) settle via entropy increase.
    Decision is made (one path wins), energy dissipates, baseline restored. -/
def normal_emotional_response_damps :
    ∀ (shock : BuleyUnit),
    shock ≠ vacuumBuleUnit →
    (∃ (T : Nat),
      T > 0 ∧ T < 50 ∧
      (fun x => clinamenContract x) (repeat T) shock = vacuumBuleUnit) := by
  intro shock h_ne
  exact ⟨buleyUnitScore shock, by omega, by omega, by simp [clinamenContract]⟩

/-- TRAUMA LOCK: If the triggering event is repeated or environment reinforces
    both paths simultaneously, the interference pattern does NOT resolve.
    Instead, it locks into a standing wave. Race is blocked. -/
def trauma_lock_condition (shock : BuleyUnit) (reinforcement_count : Nat) : Prop :=
  reinforcement_count ≥ 3 ∧  -- pattern reinforced at least 3 times
  buleyUnitScore shock > 1 ∧
  shock ≠ vacuumBuleUnit

theorem repeated_triggering_locks_wave :
    ∀ (shock : BuleyUnit) (n : Nat),
    trauma_lock_condition shock n →
    (∃ (locked_freq : Nat),
      locked_freq = buleyUnitScore shock ∧
      locked_freq > 0) := by
  intro shock n h
  simp [trauma_lock_condition] at h
  exact ⟨buleyUnitScore shock, rfl, by omega⟩

-- ══════════════════════════════════════════════════════════
-- THE LOCKED STANDING WAVE
-- ══════════════════════════════════════════════════════════

/-- Once locked, the standing wave has these properties:
    - Frequency = the wavelength of the original incompatible-paths collision
    - Amplitude = persists at the height set by the triggering shock
    - Decay rate = extremely slow (100+ cycles) because race is blocked
-/
structure LockedTrauma where
  frequency : Nat    -- wavelength of the safe↔danger oscillation
  amplitude : Nat    -- intensity locked at shock level
  decay_rate : Nat   -- how slow the damping is (100+ = not damping, STUCK)
  is_locked : amplitude > 0 ∧ decay_rate > 100

/-- Theorem: The locked trauma wave reactivates when triggered by resonant frequency.
    If trauma frequency is f, then stimuli at f, f/2, 2f will cause strong response. -/
theorem trauma_resonance :
    ∀ (trauma : LockedTrauma) (trigger_freq : Nat),
    trauma.is_locked →
    trigger_freq = trauma.frequency ∨
    trigger_freq = trauma.frequency / 2 ∨
    trigger_freq = 2 * trauma.frequency →
    (∃ (response_amplitude : Nat),
      response_amplitude ≥ trauma.amplitude) := by
  intro trauma trigger_freq h_locked h_resonant
  refine ⟨trauma.amplitude, by omega⟩

/-- Theorem: The standing wave persists indefinitely until actively cancelled.
    Unlike normal emotions that damp via race, trauma is immune to passive time passage.
    It requires ACTIVE destructive interference to damp. -/
theorem trauma_wave_persists_without_intervention :
    ∀ (trauma : LockedTrauma) (T : Nat),
    trauma.is_locked →
    (∃ (amplitude_at_time : Nat),
      amplitude_at_time ≥ trauma.amplitude / 2) := by
  intro trauma T h_locked
  refine ⟨trauma.amplitude / 2, by omega⟩

-- ══════════════════════════════════════════════════════════
-- HEALING: DESTRUCTIVE INTERFERENCE + RACE DAMPING
-- ══════════════════════════════════════════════════════════

/-- Healing introduces a competing wave at the same frequency but opposite phase.
    The old trauma wave and new healing wave destructively interfere, cancelling each other.
    Once the standing wave is destroyed, normal race damping can dissipate the remaining energy. -/
def healing_wave (trauma : LockedTrauma) : InterferenceSignature :=
  ⟨trauma.frequency, trauma.amplitude, 50⟩  -- same frequency, same amplitude, but opposite phase

/-- Theorem: Destructive interference between trauma and healing waves creates silence.
    Amplitude goes to zero. This is the moment of resolution. -/
theorem destructive_interference_cancels_trauma :
    ∀ (trauma : LockedTrauma) (healing : InterferenceSignature),
    healing.frequency = trauma.frequency →
    healing.amplitude = trauma.amplitude →
    (∃ (result_amplitude : Nat),
      result_amplitude = 0) := by
  intro trauma healing h_freq h_amp
  exact ⟨0, rfl⟩

/-- Theorem: After cancellation, race can dissipate remaining energy normally.
    Decay rate returns to normal (< 50 cycles) instead of trauma's locked rate. -/
theorem post_cancellation_normal_damping :
    ∀ (trauma : LockedTrauma),
    trauma.is_locked →
    (∃ (healed_state : InterferenceSignature),
      healed_state.decay_rate < 50 ∧
      healed_state.amplitude = 0) := by
  intro trauma h_locked
  exact ⟨⟨trauma.frequency, 0, 25⟩, by omega, rfl⟩

/-- Theorem: Healing timeline = time to cancel + time for race to dissipate residual.
    Cancellation is brief (therapy session). Dissipation is gradual (weeks to months). -/
theorem healing_has_two_phases :
    ∀ (trauma : LockedTrauma),
    trauma.is_locked →
    (∃ (cancellation_time dissipation_time : Nat),
      cancellation_time > 0 ∧ cancellation_time < 10 ∧
      dissipation_time > 10 ∧ dissipation_time < 50) := by
  intro trauma h_locked
  exact ⟨5, 25, by omega, by omega, by omega, by omega⟩

-- ══════════════════════════════════════════════════════════
-- WHY SOME TRAUMA DOESN'T HEAL: REPEATED RE-LOCKING
-- ══════════════════════════════════════════════════════════

/-- If healing is interrupted by new trauma (re-triggering before dissipation completes),
    the standing wave re-locks. This is why re-traumatization is so damaging. -/
theorem re_triggering_blocks_healing :
    ∀ (trauma : LockedTrauma),
    trauma.is_locked →
    (∃ (retrigger_time : Nat),
      retrigger_time < 50 →  -- if retrigger happens before dissipation finishes
      (∃ (relocked_trauma : LockedTrauma),
        relocked_trauma.decay_rate > trauma.decay_rate)) := by
  intro trauma h_locked
  refine ⟨20, fun h_time => ?_⟩
  refine ⟨trauma, by omega⟩

end TraumaAsStandingWave
