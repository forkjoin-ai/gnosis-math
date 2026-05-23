import Init

/-!
# VoiceCliffSusceptibility — the cliff edge is the decode-variance peak

Companion to `VoiceIntelligibilityCliff` (the plateau is a McNally Cliff, a
conjunction of thresholds) and `CrossModelCliff` (the cliff is real across model
families). Those modules treat recognition as a single binary verdict. This one
formalizes what a *sampling* decoder reveals when you stop fighting its
nondeterminism and start measuring it.

Empirical setup (`voice-bench-ensemble.py`, 2026-05-22): a synthetic clip is
transcribed K times by whisper at temperature > 0. Single-decode whisper is
nondeterministic on synthetic speech — the SAME wav decodes differently run to
run. That variation is not measurement noise to be suppressed; it is signal.

The decode-score distribution sorts every clip into one of three phases:

  * `Below` — confidently unrecognized. Stable garbage / silence. variance ≈ 0.
  * `Edge`  — critical. The decoder FLICKERS between hearing the word and not.
              variance is LARGE.
  * `Above` — confidently recognized. Stable correct. variance ≈ 0.

So decode-score variance behaves as an order-parameter susceptibility: it
vanishes in BOTH stable phases and peaks at the threshold between them — exactly
the susceptibility-at-criticality signature of a phase transition. This is why
variance localizes the cliff EDGE (and hence the highest-leverage tuning
targets) where a single binary decode cannot: the two stable phases look
identical to a thresholded judge, and identical in variance, yet opposite in
outcome. Only the variance peak marks where the transition lives.

Mechanism: per decode, "the word crosses" is approximately a Bernoulli(p) draw,
so the per-decode score variance scales as p·(1−p) — zero at p=0 and p=1,
maximal at p=1/2. We prove the shape facts below and pin them to three measured
clips.

Init-only Lean 4. Zero `sorry`, zero new `axiom`. Proven, not asserted.
-/

namespace Gnosis
namespace VoiceCliffSusceptibility

-- ══════════════════════════════════════════════════════════
-- §1  Recognition phases and measured clips
-- ══════════════════════════════════════════════════════════

/-- The phase a clip occupies under a sampling decoder. -/
inductive Phase
  | Below   -- confidently unrecognized (stable floor)
  | Edge    -- critical: decode flickers (variance peak)
  | Above   -- confidently recognized (stable ceiling)
  deriving DecidableEq, Repr

/-- One clip as measured by the ensemble judge. Probabilities and variances are
    in integer milli-units (×1000) so the file stays decidable and Init-only.
      `recog_pmille` — P(decode score ≥ 0.5) × 1000
      `var_milli`    — decode-score variance × 1000 -/
structure ClipMeasurement where
  recog_pmille : Nat
  var_milli    : Nat
  phase        : Phase
  deriving Repr

/-- `bad`: every decode is empty/garbage. Stable floor. (whisper-base K=8) -/
def bad_clip : ClipMeasurement :=
  { recog_pmille := 0, var_milli := 0, phase := Phase.Below }

/-- `fish` (F·IH·SH): decodes split across Fish! / FUSH / Peki! / …  — the
    recognizer cannot decide. Maximal decode variance: the cliff edge. -/
def fish_clip : ClipMeasurement :=
  { recog_pmille := 375, var_milli := 94, phase := Phase.Edge }

/-- `this` (DH·IH·S) after the v/z source rebalance: every decode is `This`.
    Stable ceiling — opposite outcome to `bad`, but the SAME variance floor. -/
def this_clip : ClipMeasurement :=
  { recog_pmille := 1000, var_milli := 0, phase := Phase.Above }

-- ══════════════════════════════════════════════════════════
-- §2  Diagnostics on the measured clips
-- ══════════════════════════════════════════════════════════

theorem bad_is_below  : bad_clip.phase  = Phase.Below := rfl
theorem fish_is_edge  : fish_clip.phase = Phase.Edge  := rfl
theorem this_is_above : this_clip.phase = Phase.Above := rfl

/-- The edge clip strictly exceeds the lower stable phase in decode variance. -/
theorem edge_exceeds_below : bad_clip.var_milli < fish_clip.var_milli := by decide

/-- The edge clip strictly exceeds the upper stable phase in decode variance. -/
theorem edge_exceeds_above : this_clip.var_milli < fish_clip.var_milli := by decide

/-- **The two stable phases sit at the SAME variance floor** — variance alone
    cannot tell confident-silence from confident-recognition. -/
theorem stable_phases_share_variance_floor :
    bad_clip.var_milli = this_clip.var_milli := by decide

/-- **…yet they have OPPOSITE recognition outcomes.** Together with the previous
    theorem: variance does not track the outcome, it tracks the *transition*. -/
theorem stable_phases_oppose_in_outcome :
    bad_clip.recog_pmille ≠ this_clip.recog_pmille := by decide

-- ══════════════════════════════════════════════════════════
-- §3  Why: per-decode recognition is Bernoulli, variance ∝ p·(1−p)
-- ══════════════════════════════════════════════════════════

/-- Scaled Bernoulli variance on a per-mille recognition probability:
    `p · (1000 − p)`. Peaks at p = 500, vanishes at the extremes. -/
def bernoulli_var (p : Nat) : Nat := p * (1000 - p)

theorem var_floor_at_below : bernoulli_var 0 = 0 := by decide
theorem var_floor_at_above : bernoulli_var 1000 = 0 := by decide
theorem var_peak_at_edge   : bernoulli_var 500 = 250000 := by decide

/-- The variance peak at p = 1/2 strictly dominates both extremes. -/
theorem bernoulli_peaks_at_midpoint :
    bernoulli_var 0 < bernoulli_var 500 ∧ bernoulli_var 1000 < bernoulli_var 500 := by
  decide

/-- The measured `fish` probability (p = 375‰) already sits in the high-variance
    interior, far above either floor — the empirical instance lands where the
    Bernoulli model says the susceptibility lives. -/
theorem fish_in_high_variance_interior :
    bernoulli_var 0 < bernoulli_var 375 ∧ bernoulli_var 1000 < bernoulli_var 375 := by
  decide

-- ══════════════════════════════════════════════════════════
-- §4  The principle
-- ══════════════════════════════════════════════════════════

/-- **VARIANCE-IS-THE-SUSCEPTIBILITY.**

    Across the three measured phases the Edge clip strictly exceeds BOTH stable
    phases in decode variance, while the two stable phases — opposite in
    recognition outcome (0 vs 1000 per-mille) — sit at the SAME variance floor.

    Therefore decode-score variance localizes the cliff THRESHOLD, not the
    recognition outcome: it serves as an order-parameter susceptibility that is
    maximal at criticality and vanishes in either stable phase. Operationally,
    the high-variance words are the ones one nudge from crossing — the tuning
    map the binary judge cannot produce. -/
theorem variance_is_susceptibility :
    bad_clip.var_milli = this_clip.var_milli
  ∧ bad_clip.recog_pmille ≠ this_clip.recog_pmille
  ∧ bad_clip.var_milli  < fish_clip.var_milli
  ∧ this_clip.var_milli < fish_clip.var_milli := by
  decide

end VoiceCliffSusceptibility
end Gnosis
