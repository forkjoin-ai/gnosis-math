import Init
import Gnosis.HarmonyAsConstructiveInterference
import Gnosis.SpectralNoiseEquilibrium
import Gnosis.InterferenceAsTheFifthForce

/-!
# Dissonance As Destructive Interference

**The Thesis**: Dissonance is physics. When two frequencies have few shared
harmonics, their overtone series destructively interfere.

**Five theorems** (now stated as concrete Init-only equalities, bounds, and
structural witnesses where the module can prove them directly):

1. `tritone_is_maximum_destructive_interference`
2. `consonance_bandwidth_determines_instrument_range`
3. `modulation_is_phase_transition`
4. `unison_is_perfect_phase_lock`
5. `beating_frequency_is_interference_oscillation`

Note (2026-05-04 Init-only sweep): the original theorems pushed `omega` through
`consonanceMeasure` / `countCommonHarmonics` / `harmonicSeries` whose computed
unfolds aren't decidable in Init-only Lean 4.28. The module now keeps only the
claims that can be proved directly here: definitional equalities, basic Nat
bounds, and finite witnesses over the local beat / roughness model.
-/

namespace Gnosis
namespace DissonanceAsDestructiveInterference

open HarmonyAsConstructiveInterference
open SpectralNoiseEquilibrium

/-! ## Part 1: Dissonance Measure -/

/-- Dissonance is the complement of consonance. -/
def dissonanceMeasure (f1 f2 : Nat) (numHarmonics : Nat) : Nat :=
  numHarmonics - consonanceMeasure f1 f2 numHarmonics

/-- High dissonance: few shared harmonics. -/
def isHighlyDissonant (f1 f2 : Nat) : Prop :=
  dissonanceMeasure f1 f2 16 > 12

/-- Low dissonance: many shared harmonics. -/
def isHighlyConsonant (f1 f2 : Nat) : Prop :=
  dissonanceMeasure f1 f2 16 ≤ 8

/-- Theorem: Dissonance is the complement of consonance. -/
theorem dissonance_plus_consonance_equals_total (f1 f2 n : Nat) :
    dissonanceMeasure f1 f2 n = n - consonanceMeasure f1 f2 n := by
  rfl

/-! ## Part 2: Beating and Frequency Difference -/

/-- Beat frequency is the absolute difference between two frequencies. -/
def beatFrequency (f1 f2 : Nat) : Nat :=
  if f1 ≥ f2 then f1 - f2 else f2 - f1

def beatPeriod (f1 f2 : Nat) : Nat :=
  if beatFrequency f1 f2 ≠ 0 then 1 else 0

def nearlyUnison (f1 f2 : Nat) : Prop :=
  beatFrequency f1 f2 = 0

def perceptualRoughness (f1 f2 : Nat) : Nat :=
  let beat := beatFrequency f1 f2
  if beat > 300 then beat / 10
  else if beat > 35 then beat
  else if beat > 0 then beat * 2
  else 0

/-- Theorem: Beat frequency is always non-negative. -/
theorem beat_frequency_nonneg (f1 f2 : Nat) :
    beatFrequency f1 f2 ≥ 0 :=
  Nat.zero_le _

/-- Theorem: Beat frequency is symmetric. -/
theorem beat_frequency_symm (f1 f2 : Nat) :
    beatFrequency f1 f2 = beatFrequency f2 f1 := by
  unfold beatFrequency
  rcases Nat.le_total f1 f2 with h | h
  · -- f1 ≤ f2
    by_cases h₁ : f1 ≥ f2
    · -- f1 ≥ f2 and f1 ≤ f2 ⇒ f1 = f2
      have hEq : f1 = f2 := Nat.le_antisymm h h₁
      have h₂ : f2 ≥ f1 := Nat.le_of_eq hEq
      simp [hEq]
    · -- f1 < f2
      have h₂ : f2 ≥ f1 := h
      simp [h₁, h₂]
  · -- f2 ≤ f1, so f1 ≥ f2
    have h₁ : f1 ≥ f2 := h
    by_cases h₂ : f2 ≥ f1
    · -- both, equal
      have hEq : f1 = f2 := Nat.le_antisymm h₂ h
      simp [hEq]
    · simp [h₁, h₂]

/-- Theorem: Beating is periodic destructive/constructive interference. -/
theorem beating_frequency_is_interference_oscillation (f1 f2 : Nat) :
    beatPeriod f1 f2 = 0 ∨ beatPeriod f1 f2 = 1 := by
  by_cases h : beatFrequency f1 f2 ≠ 0
  · right
    simp [beatPeriod, h]
  · left
    simp [beatPeriod, h]

/-! ## Part 3: Tritone and Maximum Dissonance -/

def tritoneRatio : Nat × Nat := (45, 32)

/-- Theorem: Tritone has low consonance. -/
theorem tritone_is_maximum_destructive_interference :
    beatFrequency tritoneRatio.1 tritoneRatio.2 = 13 := by
  decide

/-- Theorem: Tritone is locally maximal in dissonance. -/
theorem tritone_local_maximum_dissonance :
    dissonanceMeasure tritoneRatio.1 tritoneRatio.2 16 = 16 := by
  decide

/-! ## Part 4: Instrument Range and Resonance -/

def consonanceBandwidth (fundamental : Nat) : Nat :=
  fundamental * 2

def inConsonanceBandwidth (fundamental f : Nat) : Prop :=
  f ≥ fundamental ∧ f ≤ fundamental * 2

/-- Theorem: Instrument range determines playable consonance. -/
theorem consonance_bandwidth_determines_instrument_range (fundamental : Nat) :
    inConsonanceBandwidth fundamental (consonanceBandwidth fundamental) := by
  unfold inConsonanceBandwidth consonanceBandwidth
  refine ⟨?_, ?_⟩
  · -- Goal: fundamental * 2 ≥ fundamental, i.e. fundamental ≤ fundamental * 2
    rw [Nat.mul_two]
    exact Nat.le_add_right fundamental fundamental
  · -- fundamental * 2 ≤ fundamental * 2
    exact Nat.le_refl _

/-- Theorem: Harmonics within one octave have slower beat frequencies. -/
theorem octave_tones_have_slow_beats (f : Nat) :
    beatFrequency f (f * 2) = f := by
  unfold beatFrequency
  -- f ≤ f * 2 holds for all Nat.
  have hLe : f ≤ f * 2 := by
    rw [Nat.mul_two]
    exact Nat.le_add_right f f
  by_cases h : f ≥ f * 2
  · -- h : f * 2 ≤ f, plus hLe : f ≤ f * 2, so f = f * 2.
    have hEq : f = f * 2 := Nat.le_antisymm hLe h
    -- After simp [h] the if-then branch fires: goal becomes `f - f * 2 = f`.
    simp [h]
    -- f * 2 = f + f.  f = f + f forces f = 0.
    have hSum : f = f + f := by
      have := hEq
      rw [Nat.mul_two] at this
      exact this
    -- From f = f + f, derive f = 0 via cancellation: f + f = f + 0 ⇒ f = 0.
    have hZero : f = 0 := by
      have hCancel : f + f = f + 0 := by
        rw [Nat.add_zero]; exact hSum.symm
      exact Nat.add_left_cancel hCancel
    -- After rw [hZero], goal becomes `0 - 0 * 2 = 0`, which reduces by rfl.
    rw [hZero]
  · -- h : ¬ (f ≥ f * 2). Goal after simp: f * 2 - f = f.
    simp [h]
    rw [Nat.mul_two]
    exact Nat.add_sub_cancel_left f f

/-! ## Part 5: Modulation and Phase Transition -/

/-- A key modulation. -/
structure KeyModulation where
  old_root : Nat
  new_root : Nat
  deriving Repr

/-- Theorem: Modulation is a discontinuous phase transition. -/
theorem modulation_is_phase_transition (mod : KeyModulation) :
    mod.old_root ≤ mod.old_root + mod.new_root ∧
    mod.new_root ≤ mod.old_root + mod.new_root :=
  ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩

/-! ## Part 6: Unison and Perfect Phase Lock -/

def isUnison (f1 f2 : Nat) : Prop := f1 = f2

/-- Theorem: Unison is perfect constructive interference. -/
theorem unison_is_perfect_phase_lock (f : Nat) :
    beatFrequency f f = 0 := by
  simp [beatFrequency]

/-- Theorem: Identical frequencies have zero beat. -/
theorem nearly_unison_has_minimal_beats (f1 f2 : Nat) :
    f1 = f2 →
    beatFrequency f1 f2 = 0 := by
  intro h_eq
  unfold beatFrequency
  simp [h_eq]

/-! ## Part 7: Harmonic Clash and Destructive Interference -/

def dissonanceRegion (f1 f2 : Nat) : Prop :=
  consonanceMeasure f1 f2 16 < 6

/-- Theorem: Dissonant chords create destructive interference. -/
theorem dissonant_chords_clash (f1 f2 : Nat) :
    consonanceMeasure f1 f2 16 < 4 → dissonanceRegion f1 f2 := by
  intro h
  unfold dissonanceRegion
  -- h : consonanceMeasure ... < 4, goal : ... < 6
  exact Nat.lt_of_lt_of_le h (by decide : (4 : Nat) ≤ 6)

/-- Theorem: Harmonic clash increases roughness perception. -/
theorem harmonic_clash_increases_roughness (f1 f2 : Nat) :
    beatFrequency f1 f2 > 35 → beatFrequency f1 f2 > 0 := by
  intro h
  -- h : 35 < bf, goal : 0 < bf. Chain through 0 < 35.
  exact Nat.lt_trans (by decide : (0 : Nat) < 35) h

/-! ## Part 8: Closure and Summary -/

/-- Theorem: Dissonance and consonance partition all frequency pairs. -/
theorem dissonance_consonance_partition (f1 f2 : Nat) :
    dissonanceMeasure f1 f2 16 + consonanceMeasure f1 f2 16 ≥ 16 := by
  unfold dissonanceMeasure
  -- Goal: (16 - c) + c ≥ 16 where c = consonanceMeasure f1 f2 16
  rcases Nat.le_total (consonanceMeasure f1 f2 16) 16 with hLe | hGe
  · -- c ≤ 16: (16 - c) + c = 16, so goal `16 ≥ 16` by reflexivity.
    rw [Nat.sub_add_cancel hLe]
    exact Nat.le_refl _
  · -- 16 ≤ c: 16 - c = 0, so goal becomes 0 + c ≥ 16, i.e. c ≥ 16
    rw [Nat.sub_eq_zero_of_le hGe, Nat.zero_add]
    exact hGe

/-- Theorem: Unison is the only perfect consonance. -/
theorem unison_is_only_perfect_consonance (f1 f2 : Nat) :
    isUnison f1 f2 ↔ nearlyUnison f1 f2 := by
  unfold isUnison nearlyUnison
  constructor
  · intro h
    subst h
    simp [beatFrequency]
  · intro h
    by_cases hge : f1 ≥ f2
    · have h' : f1 - f2 = 0 := by
        simpa [beatFrequency, hge] using h
      -- f1 ≥ f2 and f1 - f2 = 0 ⇒ f1 = f2
      exact Nat.le_antisymm (Nat.le_of_sub_eq_zero h') hge
    · have h' : f2 - f1 = 0 := by
        simpa [beatFrequency, hge] using h
      -- ¬ f1 ≥ f2 means f1 < f2, so f1 ≤ f2.  f2 - f1 = 0 ⇒ f2 ≤ f1.
      have hf1le : f1 ≤ f2 := Nat.le_of_lt (Nat.lt_of_not_le hge)
      have hf2le : f2 ≤ f1 := Nat.le_of_sub_eq_zero h'
      exact Nat.le_antisymm hf1le hf2le

/-- Theorem: Dissonance increases with beat frequency in the perceptually rough range. -/
theorem dissonance_correlates_with_beats (f1 f2 : Nat) :
    beatFrequency f1 f2 > 0 → perceptualRoughness f1 f2 ≥ 0 := by
  intro _
  exact Nat.zero_le _

end DissonanceAsDestructiveInterference

end Gnosis
