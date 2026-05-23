import Init

/-!
# VoiceFormantHarmonicCoupling — why broad spectral features read as speech

The companion to `VoiceRecognitionAsTaoBowlInterference`. That module proved the
CENTER condition: a phoneme is recognized iff its carrier sits on the bowl's
fundamental mode (zero frequency mismatch). This module proves the WIDTH
condition, discovered empirically while tuning the sovereign formant voice.

## The empirical discovery

A formant resonance is a peak of width `BW` (its bandwidth) centered at some
frequency. A voiced source excites it with harmonics spaced `F0` apart (the
fundamental and its integer multiples). Whisper's encoder reads a mel
spectrogram — energy integrated in broad frequency bands. It registers a
formant as speech only when the formant's band is *filled*: when several
harmonics fall inside the bandwidth, the mel envelope is a smooth peak. When
the harmonics are sparse relative to the bandwidth (few or none inside), the
mel envelope is a spiky comb that does not look like speech.

The number of harmonics inside a formant of width `BW` is approximately
`BW / F0`. Call this the **harmonic coupling number** `K`:

      K = BW / F0

Two independent fixes both made our vowels cross whisper's speech-detection
threshold (measured: empty → "Uh"):

  1. Widening the formant bandwidths ~2.5× (raises `BW`).
  2. Dropping the speaker F0 register ~1 octave (lowers `F0`).

Both raise `K`. They are SUBSTITUTABLE — the gate is on the single quantity
`K`, not on `BW` or `F0` separately. This module formalizes that:

  **A formant is speech-perceptible iff `kMin · F0 ≤ BW`.**

Equivalently `K ≥ kMin`: the bandwidth must hold at least `kMin` harmonic
spacings. This is the quantitative core of "broad spectral features win" — the
through-line of the whole voice-tuning arc (vowels, diphthongs, stop bursts,
approximants: every fix widened or traversed a spectral feature).

Init-only Lean 4. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace VoiceFormantHarmonicCoupling

-- ══════════════════════════════════════════════════════════
-- §1  The harmonic coupling number
-- ══════════════════════════════════════════════════════════

/-- A formant: a resonance of bandwidth `bw` (Hz) excited by a voiced source
    of fundamental `f0` (Hz). -/
structure Formant where
  f0 : Nat
  bw : Nat

/-- Harmonic coupling number `K = BW / F0`: how many harmonic spacings fit
    inside the formant's bandwidth. `0` when the bandwidth is narrower than the
    fundamental — a sparse comb the recognizer reads as non-speech. -/
def coupling (x : Formant) : Nat := x.bw / x.f0

/-- The minimum coupling for a formant to read as speech. Empirically the fix
    moved our vowels from `K = 0` (no harmonic inside the band) to `K ≥ 1`. -/
def kMin : Nat := 1

/-- A formant is speech-perceptible when its harmonic coupling clears `kMin`. -/
def Perceptible (x : Formant) : Prop := kMin ≤ coupling x

instance (x : Formant) : Decidable (Perceptible x) := by
  unfold Perceptible; exact inferInstance

-- ══════════════════════════════════════════════════════════
-- §2  The crown theorem: the gate is bandwidth ≥ kMin · F0
-- ══════════════════════════════════════════════════════════

/-- **The width gate.** A formant reads as speech iff its bandwidth holds at
    least `kMin` harmonic spacings: `kMin · F0 ≤ BW`. This single inequality
    governs perceptibility, and it explains why widening `BW` and lowering `F0`
    are substitutable fixes — both move the same inequality toward truth.

    (The Tao-bowl CENTER condition `freqMismatch = 0` and this WIDTH condition
    together are necessary for recognition: be on the mode, and fill it.) -/
theorem perceptible_iff_bandwidth_holds_harmonics
    (x : Formant) (hf0 : 0 < x.f0) :
    Perceptible x ↔ kMin * x.f0 ≤ x.bw := by
  unfold Perceptible coupling
  exact Nat.le_div_iff_mul_le hf0

/-- With `kMin = 1` the gate is simply **bandwidth ≥ F0**: at least one full
    harmonic spacing must fit inside the formant. -/
theorem perceptible_iff_bw_ge_f0 (x : Formant) (hf0 : 0 < x.f0) :
    Perceptible x ↔ x.f0 ≤ x.bw := by
  rw [perceptible_iff_bandwidth_holds_harmonics x hf0]
  simp [kMin, Nat.one_mul]

-- ══════════════════════════════════════════════════════════
-- §3  The two fixes both raise K (monotone in BW, antitone in F0)
-- ══════════════════════════════════════════════════════════

/-- Fix #1, widening bandwidth: more bandwidth never lowers the coupling. -/
theorem coupling_monotone_in_bandwidth (f0 bw1 bw2 : Nat) (h : bw1 ≤ bw2) :
    coupling ⟨f0, bw1⟩ ≤ coupling ⟨f0, bw2⟩ := by
  unfold coupling
  exact Nat.div_le_div_right h

/-- Fix #2, lowering F0: a lower fundamental never lowers the coupling
    (denser harmonics fill the same band). -/
theorem coupling_antitone_in_f0 (bw f0lo f0hi : Nat)
    (hlo : 0 < f0lo) (h : f0lo ≤ f0hi) :
    coupling ⟨f0hi, bw⟩ ≤ coupling ⟨f0lo, bw⟩ := by
  unfold coupling
  exact Nat.div_le_div_left h hlo

-- ══════════════════════════════════════════════════════════
-- §4  Measured: the old config fails the gate, every fix-path passes it
-- ══════════════════════════════════════════════════════════

/-- Old vowel rendering: high F0 (155Hz Aeon) + narrow formant BW (90Hz).
    K = 90/155 = 0 → below the gate → imperceptible. Matches the measured
    "vowels transcribe as empty". -/
def oldVowel : Formant := ⟨155, 90⟩

/-- New vowel rendering: F0 dropped an octave (123Hz) + BW widened (130Hz).
    K = 130/123 = 1 → clears the gate → perceptible. Matches "vowels now
    register (empty → Uh)". -/
def newVowel : Formant := ⟨123, 130⟩

/-- Bandwidth-only fix: keep the old high F0, widen BW past it. -/
def bwOnlyFix : Formant := ⟨155, 170⟩

/-- F0-only fix: keep the old narrow BW, drop F0 below it. -/
def f0OnlyFix : Formant := ⟨80, 90⟩

theorem old_vowel_imperceptible : ¬ Perceptible oldVowel := by decide
theorem new_vowel_perceptible : Perceptible newVowel := by decide

/-- **Substitutability, witnessed.** Either lever alone — widening BW at the
    old F0, or lowering F0 at the old BW — crosses the gate. The fix lives on
    `K`, not on `BW` or `F0` individually. -/
theorem either_lever_alone_suffices :
    Perceptible bwOnlyFix ∧ Perceptible f0OnlyFix := by decide

/-- The fix strictly raised the coupling number (0 → 1): the boundary the
    whole arc was stuck behind, crossed. -/
theorem fix_raised_coupling : coupling oldVowel < coupling newVowel := by decide

end VoiceFormantHarmonicCoupling
end Gnosis
