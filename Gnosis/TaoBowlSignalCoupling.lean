import Gnosis.EchoChamberAsTaoBowl
import Gnosis.OpinionAsInterference
import Gnosis.EchoChamberAsStandingWave

/-
  TaoBowlSignalCoupling.lean
  ==========================

  Couples an `OpinionWave` (frequency + confidence as amplitude) to the
  Tao-bowl resonance filter (`EchoChamberAsTaoBowl.filteredAmplitude`):
  the bowl maps external opinion carrier frequency and confidence through
  the same mismatch / Q / damping bookkeeping used for scalar signals.

  Standing-wave echo chambers (`EchoChamberAsStandingWave`) expose a
  different numeric filter on external waves (`external_info_destructive_interference`,
  coherence-weighted). This module keeps the bridge honest: frequency
  alignment with `chamberOfBowl` is alignment with `fundamentalMode`, and
  the bowl's off-mode branch is exactly the damped `filteredAmplitude` path.

  Imports upstream bowl, opinion, and standing-wave layers. Zero `sorry`,
  zero new `axiom`.
-/


namespace TaoBowlSignalCoupling

open EchoChamberAsTaoBowl
open OpinionAsInterference
open EchoChamberAsStandingWave

/-- Post-bowl amplitude for an opinion wave: frequency and confidence pass
    through `filteredAmplitude`. -/
def bowlActsOn (b : TaoBowl) (w : OpinionWave) : Nat :=
  filteredAmplitude b w.frequency w.confidence

theorem bowlActsOn_eq_filtered (b : TaoBowl) (w : OpinionWave) :
    bowlActsOn b w = filteredAmplitude b w.frequency w.confidence := by
  rfl

theorem bowlActsOn_freqMismatch_zero (b : TaoBowl) (w : OpinionWave)
    (h : freqMismatch b w.frequency = 0) :
    bowlActsOn b w = w.confidence * qFactor b := by
  unfold bowlActsOn filteredAmplitude
  simp [h]

/-! ### Frequency mismatch vs fundamental mode -/

theorem freqMismatch_eq_zero_iff_fundamental (b : TaoBowl) (f : Nat) :
    freqMismatch b f = 0 ↔ f = fundamentalMode b := by
  let m := fundamentalMode b
  unfold freqMismatch
  constructor
  · intro h
    by_cases hle : m ≤ f
    · rw [if_pos hle] at h
      have hfm : f ≤ m := (Nat.sub_eq_zero_iff_le).mp h
      exact Nat.le_antisymm hfm hle
    · rw [if_neg hle] at h
      have hmle : m ≤ f := (Nat.sub_eq_zero_iff_le).mp h
      exact absurd hmle hle
  · intro hf
    subst hf
    simp [Nat.le_refl]

/-! ### `chamberOfBowl` center frequency equals `fundamentalMode` -/

theorem chamberOfBowl_center_frequency (b : TaoBowl) :
    (chamberOfBowl b ([] : List OpinionWave)).center_frequency =
      fundamentalMode b := by
  rfl

theorem frequency_eq_chamber_center_iff_freqMismatch_zero (b : TaoBowl)
    (w : OpinionWave) :
    w.frequency = (chamberOfBowl b ([] : List OpinionWave)).center_frequency ↔
      freqMismatch b w.frequency = 0 := by
  rw [chamberOfBowl_center_frequency b]
  exact (freqMismatch_eq_zero_iff_fundamental b w.frequency).symm

/-! ### Standing-wave "external" predicate ↔ nonzero bowl mismatch -/

theorem is_external_information_chamberOfBowl_iff_freqMismatch_ne_zero
    (b : TaoBowl) (w : OpinionWave) :
    is_external_information w (chamberOfBowl b ([] : List OpinionWave)) ↔
      freqMismatch b w.frequency ≠ 0 := by
  unfold is_external_information
  rw [chamberOfBowl_center_frequency b]
  constructor
  · intro hfreq hmiss
    exact hfreq ((freqMismatch_eq_zero_iff_fundamental b w.frequency).mp hmiss)
  · intro hneq heq
    exact hneq ((freqMismatch_eq_zero_iff_fundamental b w.frequency).mpr heq)

/-! ### Bowl off-mode branch when information is external (composition) -/

theorem bowlActsOn_external_eq_damped (b : TaoBowl) (w : OpinionWave)
    (h : is_external_information w (chamberOfBowl b ([] : List OpinionWave))) :
    bowlActsOn b w = w.confidence / (b.damping + 1) := by
  have hmiss : freqMismatch b w.frequency ≠ 0 :=
    (is_external_information_chamberOfBowl_iff_freqMismatch_ne_zero b w).mp h
  unfold bowlActsOn filteredAmplitude
  rw [if_neg hmiss]

theorem external_info_destructive_interference_chamberOfBowl (b : TaoBowl)
    (w : OpinionWave) :
    external_info_destructive_interference w (chamberOfBowl b ([] : List OpinionWave)) =
      (w.confidence * (chamberOfBowl b ([] : List OpinionWave)).coherence) / 100 := by
  rfl

/-- Coherence-weighted standing-wave filter is strictly positive once the
    raw product reaches 100 (so Nat division is at least 1). -/
theorem external_filter_positive (b : TaoBowl) (w : OpinionWave)
    (hprod : 100 ≤ w.confidence * (chamberOfBowl b ([] : List OpinionWave)).coherence) :
    0 < external_info_destructive_interference w
        (chamberOfBowl b ([] : List OpinionWave)) := by
  unfold external_info_destructive_interference
  have hone :
      1 ≤
        (w.confidence * (chamberOfBowl b ([] : List OpinionWave)).coherence) / 100 := by
    rw [Nat.le_div_iff_mul_le (by decide : 0 < 100)]
    simpa using hprod
  exact Nat.lt_of_succ_le hone

end TaoBowlSignalCoupling
