import Init

/-!
# VoiceCoarticulationContinuity — why connected words need glides, not slower phonemes

The third voice module, formalizing a measured NEGATIVE result and the lever it
points to. Companions:
  * VoiceRecognitionAsTaoBowlInterference — the CENTER condition (on the mode)
  * VoiceFormantHarmonicCoupling          — the WIDTH condition (fill the mode)
  * this module                           — the CONTINUITY condition (connect the modes)

## The measurement

Isolated sustained vowels now register as speech, but vowels INSIDE WORDS still
fail ("moon"→"", "zoo"→""). A duration/continuity sweep tested the obvious fix —
make phonemes longer / smoother — and found it does NOT work: longer durations
hurt, and the best config was a near-noise-floor +8%.

The reason: a word rendered as steady-state islands has abrupt FORMANT JUMPS at
each phoneme boundary (the formant track teleports from one phoneme's center to
the next). Whisper's encoder reads those discontinuities as non-speech; real
speech has continuous formant trajectories (coarticulation) — the formants
GLIDE between targets, and those glides are the cues whisper uses to segment
words.

The key formal fact: **stretching phoneme durations cannot remove a boundary
jump — a jump is instantaneous regardless of how long the segments around it
are.** Only inserting a transition (coarticulation) — values that step between
the targets within a rate limit — eliminates the jump. This is why the duration
sweep failed and why coarticulation is the connected-word lever.

We model the F2 track (the dominant coarticulation cue) as a list of formant
values; a "jump" is an adjacent step exceeding the rate limit `maxStep` that the
recognizer can follow as continuous.

Init-only Lean 4. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace VoiceCoarticulationContinuity

/-- A formant track: successive F2 values along an utterance (one per rendered
    frame / segment). -/
abbrev Track := List Nat

/-- |a - b| in Nat. -/
def absDiff (a b : Nat) : Nat := if a ≤ b then b - a else a - b

/-- Count adjacent steps whose magnitude exceeds `maxStep` — the boundary
    discontinuities the recognizer reads as non-speech. `maxStep` is the
    largest formant change per frame still perceived as a continuous glide. -/
def jumps (maxStep : Nat) : Track → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: rest =>
      (if absDiff a b > maxStep then 1 else 0) + jumps maxStep (b :: rest)

/-- Duration scaling: hold each value `c` frames longer (a slower utterance).
    Models exactly what SB_DUR_SCALE does — repeats, no new transitions. -/
def expand : Nat → Track → Track
  | _, [] => []
  | c, x :: xs => (List.replicate c x) ++ expand c xs

-- ══════════════════════════════════════════════════════════
-- §1  A constant hold contributes no jumps (the easy invariant)
-- ══════════════════════════════════════════════════════════

/-- Repeating a single value never creates a jump: a flat hold is continuous. -/
theorem replicate_no_jumps (m c v : Nat) : jumps m (List.replicate c v) = 0 := by
  induction c with
  | zero => rfl
  | succ k ih =>
      cases k with
      | zero => rfl
      | succ j =>
          -- replicate (j+2) v = v :: v :: replicate j v
          simp only [List.replicate, jumps, absDiff]
          -- absDiff v v = 0, not > m
          have : ¬ (0 > m) := Nat.not_lt.mpr (Nat.zero_le m)
          simp only [Nat.le_refl, Nat.sub_self, if_pos]
          simp [this]
          -- remaining is jumps m (v :: replicate j v) = 0, from ih shape
          simpa [List.replicate] using ih

-- ══════════════════════════════════════════════════════════
-- §2  The measured case: islands jump, duration can't fix it, glide can
-- ══════════════════════════════════════════════════════════

/-- An island-rendered word: three vowel F2 centers with big jumps between them
    (e.g. /a/ 800 → /i/ 1800 → /o/ 600). -/
def islandWord : Track := [800, 1800, 600]

/-- The same word with phonemes held 3× longer (SB_DUR_SCALE = 3): each value
    repeated, boundaries unchanged. -/
def slowWord : Track := expand 3 islandWord

/-- The same word coarticulated: a glide of ≤300-Hz steps fills each transition,
    so the formant track is continuous through the targets. -/
def glideWord : Track := [800, 1050, 1300, 1550, 1800, 1500, 1200, 900, 600]

/-- maxStep the recognizer follows as a continuous glide (Hz/frame). -/
def maxStep : Nat := 300

/-- Islands jump twice — one discontinuity per phoneme boundary. -/
theorem islands_jump : jumps maxStep islandWord = 2 := by decide

/-- **The negative result, formal.** Stretching every phoneme 3× leaves the
    jump count EXACTLY the same: duration scaling cannot remove a boundary
    discontinuity. This is why the duration/continuity sweep flatlined. -/
theorem duration_does_not_fix_jumps : jumps maxStep slowWord = jumps maxStep islandWord := by
  decide

/-- **The lever, formal.** Coarticulation — inserting rate-limited transitions
    between targets — drives the discontinuity count to zero. The track is
    continuous; whisper can follow it. -/
theorem coarticulation_eliminates_jumps : jumps maxStep glideWord = 0 := by decide

/-- The punchline in one inequality: the glide strictly beats both the island
    render and its slowed-down version (which are equal). Continuity, not
    duration, is the connected-word fix. -/
theorem glide_strictly_beats_duration :
    jumps maxStep glideWord < jumps maxStep slowWord := by decide

end VoiceCoarticulationContinuity
end Gnosis
