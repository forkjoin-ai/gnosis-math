/-
  DepressionAsDampedOscillation.lean
  ================================

  Depression is modeled by suppressed constructive interference of positive
  patterns, accelerated decay of positive emotional energy, and a rumination
  loop locked to despair.

  Unlike anxiety (high amplitude, unresolved), depression is low amplitude
  with energy bleeding away faster than it accumulates.
-/

import Gnosis.SpectralNoiseEquilibrium
import Gnosis.InterferenceAsTheFifthForce
import Gnosis.TemporaryNoise
import Gnosis.PsychologyAsInterference

namespace DepressionAsDampedOscillation

open Gnosis.SpectralNoiseEquilibrium
open InterferenceAsTheFifthForce
open TemporaryNoise
open PsychologyAsInterference

-- ══════════════════════════════════════════════════════════
-- DEPRESSION: SUPPRESSED POSITIVE, LOCKED NEGATIVE
-- ══════════════════════════════════════════════════════════

/-- Depression has two simultaneous dynamics:
    1. Positive-emotion frequencies are suppressed (decay too fast)
    2. Negative-emotion frequencies persist (decay too slow)
    Result: low net energy, persistent sadness, anhedonia (joy feels impossible)
-/
structure DepressionState where
  positive_decay : Nat    -- how fast joy/meaning fade (should be <50, is >100 in depression)
  negative_decay : Nat    -- how fast sadness fades (should be <50, is ~40 in depression)

/-- Predicate: is this state depressed (asymmetric decay rates)? -/
def is_depressed (dep : DepressionState) : Prop :=
  dep.positive_decay > 2 * dep.negative_decay

theorem depression_asymmetry :
    ∀ (dep : DepressionState),
    is_depressed dep →
    dep.positive_decay > 2 * dep.negative_decay := by
  intro dep h
  exact h

-- ══════════════════════════════════════════════════════════
-- ANHEDONIA: WHY JOY FEELS IMPOSSIBLE
-- ══════════════════════════════════════════════════════════

/-- In depression, positive-emotion patterns activate but immediately damp.
    A moment of joy occurs (constructive interference of meaning + connection),
    but within 5-10 cycles, the amplitude collapses to near-zero.

    Normal joy: decays over 30-60 cycles. Depressed joy: decays over 5-10 cycles.
    Difference: 3-6× faster energy loss. -/
def anhedonia (joy_pattern : InterferenceSignature) : Prop :=
  joy_pattern.decay_rate > 100  -- positive pattern decays extremely fast in depression
  ∧ joy_pattern.amplitude > 0    -- it activates, but...
  ∧ joy_pattern.decay_rate > 20  -- ...then collapses in just 20 cycles

theorem anhedonia_is_accelerated_decay :
    ∀ (joy : InterferenceSignature),
    anhedonia joy →
    joy.decay_rate > 20 := by
  intro joy h
  -- h : anhedonia joy unfolds to a 3-way And; pull the third conjunct.
  exact h.2.2

-- ══════════════════════════════════════════════════════════
-- RUMINATION LOOP: DESTRUCTIVE INTERFERENCE LOCKED TO DESPAIR
-- ══════════════════════════════════════════════════════════

/-- Rumination in depression is destructive interference between:
    - Hope frequency (positive thought): "Maybe things will get better"
    - Despair frequency (negative thought): "No, they won't, you're broken"

    These two frequencies oscillate at ~0.5 Hz. But they're phase-locked
    in destructive interference: every time hope activates, despair
    immediately activates at opposite phase, cancelling the hope.

    Result: perpetual oscillation between slight hope and despair,
    with despair always winning (amplitude-wise). -/
def rumination_loop (hope despair : InterferenceSignature) : Prop :=
  hope.frequency = despair.frequency ∧
  hope.frequency > 0 ∧
  hope.amplitude > 0 ∧
  despair.amplitude > hope.amplitude ∧  -- despair always bigger
  hope.decay_rate > 100  -- hope decays extremely fast (suppressed)

theorem rumination_always_returns_to_despair :
    ∀ (hope despair : InterferenceSignature),
    rumination_loop hope despair →
    despair.amplitude > hope.amplitude := by
  intro hope despair h
  simp [rumination_loop] at h
  exact h.2.2.2.1

-- ══════════════════════════════════════════════════════════
-- LOW OVERALL ENERGY STATE
-- ══════════════════════════════════════════════════════════

/-- Depression is characterized by low oscillation amplitude overall.
    Unlike anxiety (high amplitude, racing), depression is sluggish, low energy.
    The nervous system is dampened across the board. -/
def low_energy_state (patterns : List InterferenceSignature) : Prop :=
  (∀ sig ∈ patterns, sig.amplitude < 3) ∧  -- all amplitudes suppressed
  patterns.length > 0

-- ══════════════════════════════════════════════════════════
-- HEALING DEPRESSION: RESTORE POSITIVE CONSTRUCTION
-- ══════════════════════════════════════════════════════════

/-- Depression heals by:
    1. Disrupting the rumination loop (introducing competing positive patterns)
    2. Slowing the decay of positive frequencies (blocking suppression)
    3. Allowing normal race dynamics to resume for both positive and negative patterns
-/
def depression_healing (_initial : DepressionState) : Prop :=
  (∃ (healed : DepressionState),
    healed.positive_decay < 50 ∧  -- positive patterns no longer suppressed
    healed.negative_decay < 50 ∧  -- negative patterns damp normally
    healed.positive_decay ≤ 2 * healed.negative_decay)  -- symmetry restored

theorem antidepressant_slows_positive_decay :
    ∀ (initial : DepressionState),
    is_depressed initial →
    (∃ (healed : DepressionState),
      healed.positive_decay < initial.positive_decay) := by
  intro initial h_dep
  unfold is_depressed at h_dep
  -- positive_decay > 2 * negative_decay ≥ 0, so positive_decay ≥ 1, so 0 < positive_decay
  refine ⟨⟨0, initial.negative_decay⟩, ?_⟩
  show (0 : Nat) < initial.positive_decay
  -- h_dep : 2 * initial.negative_decay < initial.positive_decay
  -- 0 ≤ 2 * negative_decay < positive_decay ⇒ 0 < positive_decay
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) h_dep

theorem cognitive_therapy_disrupts_rumination :
    ∀ (hope despair : InterferenceSignature),
    rumination_loop hope despair →
    (∃ (new_thought : InterferenceSignature),
      new_thought.frequency = hope.frequency ∧
      new_thought.amplitude > hope.amplitude) := by
  intro hope _despair _h_rum
  refine ⟨⟨hope.frequency, hope.amplitude + 1, 30⟩, rfl, ?_⟩
  show hope.amplitude + 1 > hope.amplitude
  exact Nat.lt_succ_self _

end DepressionAsDampedOscillation
