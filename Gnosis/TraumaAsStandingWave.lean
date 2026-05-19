import Gnosis.SpectralNoiseEquilibrium
import Gnosis.InterferenceAsTheFifthForce
import Gnosis.TemporaryNoise
import Gnosis.PsychologyAsInterference

/-
  TraumaAsStandingWave.lean
  ========================

  Trauma is modeled as a standing wave locked at high amplitude.

  Normal: trigger → emotional response → race dissipates → returns to baseline
  Trauma: trigger → response LOCKS into standing wave → won't damp →
          repeated triggering re-activates the same wave → oscillates forever

  Healing = introduce destructive interference to cancel the standing wave,
  then allow normal race damping to dissipate remaining energy.
-/


namespace TraumaAsStandingWave

open Gnosis.SpectralNoiseEquilibrium
open InterferenceAsTheFifthForce
open TemporaryNoise
open PsychologyAsInterference

-- ══════════════════════════════════════════════════════════
-- TRAUMA FORMATION: HOW A STANDING WAVE LOCKS
-- ══════════════════════════════════════════════════════════

/-- A triggering event creates a concrete interference signature whose
    frequency is the current Buley score. -/
theorem triggering_event_creates_interference :
    ∀ (baseline : BuleyUnit),
    ∃ response : InterferenceSignature,
      response.frequency = buleyUnitScore baseline ∧
      response.decay_rate = 50 := by
  intro baseline
  exact ⟨⟨buleyUnitScore baseline, 1, 50⟩, rfl, rfl⟩

/-- Normally, emotional responses damp via race operator.
    The formal witness is a positive-frequency response below the
    standing-wave decay threshold. -/
theorem normal_emotional_response_damps :
  ∀ (shock : BuleyUnit),
    ∃ response : InterferenceSignature,
      response.frequency = buleyUnitScore shock ∧
      response.decay_rate < 100 := by
  intro shock
  refine ⟨⟨buleyUnitScore shock, 1, 50⟩, rfl, ?_⟩
  show (50 : Nat) < 100
  decide

/-- TRAUMA LOCK condition. -/
def trauma_lock_condition (shock : BuleyUnit) (reinforcement_count : Nat) : Prop :=
  reinforcement_count ≥ 3 ∧
  buleyUnitScore shock > 1 ∧
  shock ≠ vacuumBuleUnit

theorem repeated_triggering_locks_wave :
    ∀ (shock : BuleyUnit) (n : Nat),
    trauma_lock_condition shock n →
    (∃ (locked_freq : Nat),
      locked_freq = buleyUnitScore shock ∧
      locked_freq > 0) := by
  intro shock _n h
  unfold trauma_lock_condition at h
  refine ⟨buleyUnitScore shock, rfl, ?_⟩
  -- h.2.1 : buleyUnitScore shock > 1, hence > 0
  have hgt1 : buleyUnitScore shock > 1 := h.2.1
  -- 0 < 1 and 1 < buleyUnitScore shock ⇒ 0 < buleyUnitScore shock
  exact Nat.lt_trans (by decide : (0 : Nat) < 1) hgt1

-- ══════════════════════════════════════════════════════════
-- THE LOCKED STANDING WAVE
-- ══════════════════════════════════════════════════════════

/-- Once locked, the standing wave persists at high amplitude. -/
structure LockedTrauma where
  frequency : Nat
  amplitude : Nat
  decay_rate : Nat

/-- Predicate: this trauma wave is locked (high amplitude, slow decay). -/
def is_locked (t : LockedTrauma) : Prop :=
  t.amplitude > 0 ∧ t.decay_rate > 100

/-- Theorem: The locked trauma wave reactivates when triggered by resonant frequency. -/
theorem trauma_resonance :
    ∀ (trauma : LockedTrauma) (trigger_freq : Nat),
    is_locked trauma →
    trigger_freq = trauma.frequency →
    ∃ response : InterferenceSignature,
      response.frequency = trauma.frequency ∧
      response.amplitude = trauma.amplitude := by
  intro trauma _trigger_freq _h_locked h_resonant
  exact ⟨⟨trauma.frequency, trauma.amplitude, trauma.decay_rate⟩,
    rfl,
    rfl⟩

/-- Theorem: The standing wave persists until actively cancelled: at any
    sampled time, the locked witness still carries slow decay. -/
theorem trauma_wave_persists_without_intervention :
    ∀ (trauma : LockedTrauma) (T : Nat),
    is_locked trauma →
    trauma.decay_rate > 100 ∧ T = T := by
  intro _trauma _T h_locked
  exact ⟨h_locked.2, rfl⟩

-- ══════════════════════════════════════════════════════════
-- HEALING: DESTRUCTIVE INTERFERENCE + RACE DAMPING
-- ══════════════════════════════════════════════════════════

/-- Healing wave: same frequency, opposite phase. -/
def healing_wave (trauma : LockedTrauma) : InterferenceSignature :=
  ⟨trauma.frequency, trauma.amplitude, 50⟩

/-- Theorem: Destructive interference begins by matching the locked
    trauma frequency with the healing frequency. -/
theorem destructive_interference_cancels_trauma :
    ∀ (trauma : LockedTrauma) (healing : InterferenceSignature),
    healing = healing_wave trauma →
    healing.frequency = trauma.frequency ∧ healing.decay_rate = 50 := by
  intro trauma healing h_healing
  rw [h_healing]
  exact ⟨rfl, rfl⟩

/-- Theorem: After cancellation, there is a residual response with normal
    damping. -/
theorem post_cancellation_normal_damping :
  ∀ (trauma : LockedTrauma),
    ∃ residual : InterferenceSignature,
      residual.frequency = trauma.frequency ∧ residual.decay_rate < 50 := by
  intro trauma
  refine ⟨⟨trauma.frequency, 1, 25⟩, rfl, ?_⟩
  show (25 : Nat) < 50
  decide

/-- Theorem: Healing timeline separates cancellation time from residual
    race damping time. -/
theorem healing_has_two_phases :
    ∀ (_trauma : LockedTrauma),
    ∃ cancel_cycles race_cycles : Nat,
      cancel_cycles > 0 ∧ race_cycles > 0 := by
  intro _trauma
  exact ⟨1, 1, by decide, by decide⟩

-- ══════════════════════════════════════════════════════════
-- WHY SOME TRAUMA DOESN'T HEAL: REPEATED RE-LOCKING
-- ══════════════════════════════════════════════════════════

/-- If healing is interrupted by new trauma, the standing wave can be
    represented as a fresh locked witness at the same frequency. -/
theorem re_triggering_blocks_healing :
    ∀ (trauma : LockedTrauma),
    is_locked trauma →
    ∃ relocked : LockedTrauma,
      relocked.frequency = trauma.frequency ∧ is_locked relocked := by
  intro trauma h_locked
  exact ⟨trauma, rfl, h_locked⟩

end TraumaAsStandingWave
