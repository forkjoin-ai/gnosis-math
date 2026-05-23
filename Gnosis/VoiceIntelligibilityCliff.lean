import Init

/-!
# VoiceIntelligibilityCliff — the plateau is a McNally Cliff, not a gradient

Capstone of the voice trilogy. The three conditions, each its own module:
  * VoiceRecognitionAsTaoBowlInterference — CENTER    (on the resonant mode)
  * VoiceFormantHarmonicCoupling          — WIDTH     (fill the mode: BW ≥ kMin·F0)
  * VoiceCoarticulationContinuity         — CONTINUITY (connect modes with glides)

Empirically, tuning the sovereign voice plateaued: the whisper-word benchmark
sat at ~0.10 across many changes (wide BW, low F0, vowel retuning, stop bursts),
and one change (crude coarticulation) dropped it. Taylor's reading: **the
plateau is real — a real signal, not measurement noise — and it is a McNally
Cliff** (`CrossModelCliff`, `AtlasGeneralization`): a sharp DC-cliff in a
capability landscape, flat floor then sudden edge.

Why a cliff and not a smooth gradient? Because word recognition is the
CONJUNCTION of the three conditions, each a threshold:

      recognized  ⟺  onMode ∧ filled ∧ connected

A conjunction over thresholds has no partial credit. Satisfy two of three and
you get the FLOOR (whisper's no-speech hallucination baseline, ~0.10) — exactly
the plateau. Improving an already-met condition, or pushing harder on one while
another stays false, moves nothing: you slide along the flat cliff bottom.
Only completing the LAST unmet condition crosses the edge and the score jumps.

Our measured state: onMode ✓ (resonance), filled ✓ (wide BW + low F0), but
connected ✗ (no working coarticulation — the crude attempt regressed). Two of
three ⇒ cliff floor. The edge is reached exactly when `connected` flips true.
That is why incremental phoneme tuning is futile here and why the remaining
lever is specifically continuity.

Init-only Lean 4. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace VoiceIntelligibilityCliff

-- ══════════════════════════════════════════════════════════
-- §1  The three conditions and the conjunction
-- ══════════════════════════════════════════════════════════

/-- The acoustic conditions a synthetic voice must meet to be recognized,
    one per voice module. -/
structure VoiceState where
  onMode    : Bool  -- carrier on the recognizer's resonant mode (CENTER)
  filled    : Bool  -- bandwidth holds enough harmonics (WIDTH)
  connected : Bool  -- formant track continuous across boundaries (CONTINUITY)
  deriving DecidableEq, Repr

/-- Word recognition is the CONJUNCTION of all three. No partial credit. -/
def recognized (s : VoiceState) : Bool :=
  s.onMode && s.filled && s.connected

/-- The intelligibility score is a CLIFF: the hallucination floor unless all
    three conditions hold, then the recognized height. (`floor`/`peak` stand in
    for the ~0.10 vs intelligible bench scores, in integer per-mille.) -/
def floor : Nat := 100   -- ~0.10: whisper no-speech hallucination baseline
def peak  : Nat := 800   -- recognized
def score (s : VoiceState) : Nat := if recognized s then peak else floor

-- ══════════════════════════════════════════════════════════
-- §2  The cliff: no partial credit
-- ══════════════════════════════════════════════════════════

/-- **The plateau is the floor.** Any state missing even one condition scores
    exactly the floor — identical to any other under-spec state. This is the
    flat cliff bottom: measurements cluster at one value regardless of which
    conditions are (partially) improved. -/
theorem incomplete_is_floor (s : VoiceState) (h : recognized s = false) :
    score s = floor := by
  simp [score, h]

/-- **Two of three is still the floor.** Our measured state — on the mode and
    filled, but not connected — scores the floor, indistinguishable from the
    void. Improving CENTER or WIDTH further cannot move it. -/
theorem center_and_width_without_continuity_is_floor :
    score ⟨true, true, false⟩ = floor := by decide

/-- **Only the complete conjunction reaches the edge.** The single state that
    clears the cliff is all-three-true. -/
theorem only_all_three_reaches_peak (s : VoiceState) :
    score s = peak ↔ s = ⟨true, true, true⟩ := by
  constructor
  · intro h
    -- score = peak ⇒ recognized ⇒ all three true
    unfold score at h
    by_cases hr : recognized s
    · unfold recognized at hr
      -- hr : (s.onMode && s.filled && s.connected) = true
      have h1 : s.onMode = true ∧ s.filled = true ∧ s.connected = true := by
        revert hr; cases s.onMode <;> cases s.filled <;> cases s.connected <;> simp
      cases s; simp_all
    · rw [if_neg hr] at h
      -- floor = peak is false
      exact absurd h (by decide)
  · intro h; subst h; decide

/-- **The cliff edge is exactly the continuity flip.** Given CENTER and WIDTH
    already met (our state), the score jumps from floor to peak the instant
    CONTINUITY becomes true — a step function, not a ramp. This is the formal
    statement of "the remaining lever is coarticulation, and it pays nothing
    until it works, then it pays all at once." -/
theorem edge_is_the_continuity_flip :
    score ⟨true, true, false⟩ = floor ∧ score ⟨true, true, true⟩ = peak := by
  decide

/-- The jump is strictly positive: crossing the edge is a real gain, and
    `peak > floor` makes the cliff a cliff (not a degenerate flat line). -/
theorem cliff_has_height : floor < peak := by decide

end VoiceIntelligibilityCliff
end Gnosis
