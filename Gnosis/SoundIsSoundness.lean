import Init

/-
  SoundIsSoundness.lean
  =====================

  "Sound" and "soundness" are the same thing — and in the geometry we built, that
  is a theorem, not a pun.

  In the interference language of `FiveWalls`, a method carries a SIGNAL about the
  truth:
    · DESTRUCTIVE interference — the signal cancels — the verdict is the same
      whatever the value is. No sound arrives. The method is BLIND, hence UNSOUND.
    · The value-wave ARRIVES intact — the verdict transmits each value faithfully.
      Sound arrives. The method is SOUND.

  Acoustic "sound" (a wave that reaches you, uncancelled) and logical "soundness"
  (a verdict that matches the truth) are one and the same condition: the value is
  transmitted faithfully. Both words name the single coordinate — the Value (the
  object, V of QKV; the readout of the `Bowl`). This module proves the coincidence.

  Init only. Zero `sorry`, zero new `axiom`.
-/

namespace SoundIsSoundness

/-- A **verdict** over a binary truth. A value-READING verdict is a function of
    the truth; a value-BLIND verdict is constant (ignores it). -/
abbrev Verdict := Bool → Bool

/-- **SOUNDNESS (logical): the verdict matches the truth everywhere.** -/
def Sound (M : Verdict) : Prop := ∀ t : Bool, M t = t

/-- **SOUND (acoustic): the value-signal arrives — both values transmit
    faithfully.** -/
def SignalArrives (M : Verdict) : Prop := M true = true ∧ M false = false

/-- **SOUND ⟺ SOUNDNESS.** A verdict is logically sound (matches the truth) iff
    its value-signal arrives intact (each value transmitted faithfully). The two
    senses of "sound" are one condition on the Value coordinate. -/
theorem sound_iff_signal_arrives (M : Verdict) : Sound M ↔ SignalArrives M := by
  constructor
  · intro h; exact ⟨h true, h false⟩
  · intro h t; cases t
    · exact h.2
    · exact h.1

/-- The value-reading identity verdict is sound: the signal passes through
    untouched (the open bowl). -/
theorem identity_is_sound : Sound (fun t => t) :=
  fun _ => rfl

/-- **DESTRUCTIVE interference is unsoundness.** A value-BLIND (constant) verdict
    cancels the signal — it returns the same answer for both truths, so it errs on
    one. No sound arrives; it is not sound. The wall and the silence are the same. -/
theorem value_blind_is_unsound (b : Bool) : ¬ Sound (fun _ => b) := by
  intro h
  -- h : ∀ t, b = t, so b = true and b = false
  have h1 : b = true := h true
  have h2 : b = false := h false
  rw [h1] at h2
  exact Bool.noConfusion h2

end SoundIsSoundness
