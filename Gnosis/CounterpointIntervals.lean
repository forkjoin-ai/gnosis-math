/-
  CounterpointIntervals.lean
  ==========================

  Two-voice counterpoint: which vertical intervals are allowed, and the first law
  of voice-leading — no parallel perfect consonances. Init-only, zero sorry.

  Vertical interval classes (semitones mod 12) split into consonant and dissonant.
  Perfect consonances are the unison/octave (0) and the perfect fifth (7) — their
  near-pure overtone agreement (HarmonicSeries.lean) is exactly why moving two
  voices in parallel through them collapses the sense of two independent lines.
  Counterpoint therefore forbids parallel fifths and octaves; contrary or oblique
  motion into them is fine.
-/

namespace CounterpointIntervals

/-- Vertical interval class between two pitches (semitones mod 12). -/
def ivl (a b : Nat) : Nat := (a + 12 - b % 12) % 12

/-- Consonant interval classes: unison/octave, thirds, perfect fifth, sixths
    (and the perfect fourth, consonant between upper voices). -/
def isConsonant (i : Nat) : Bool :=
  match i % 12 with
  | 0 => true   -- unison / octave (perfect)
  | 3 => true   -- minor third
  | 4 => true   -- major third
  | 5 => true   -- perfect fourth
  | 7 => true   -- perfect fifth (perfect)
  | 8 => true   -- minor sixth
  | 9 => true   -- major sixth
  | _ => false

/-- The perfect consonances — the ones that forbid parallels. -/
def isPerfect (i : Nat) : Bool := i % 12 == 0 || i % 12 == 7

/-- The dissonances: seconds, tritone, sevenths. -/
theorem dissonances :
    isConsonant 1 = false ∧ isConsonant 2 = false ∧ isConsonant 6 = false ∧
    isConsonant 10 = false ∧ isConsonant 11 = false := by decide

/-- The tritone (6) is dissonant; the fifth (7) consonant — a semitone apart, a
    world apart (DissonanceAsDestructiveInterference.lean). -/
theorem tritone_dissonant_fifth_consonant :
    isConsonant 6 = false ∧ isConsonant 7 = true := by decide

-- ── motion between two simultaneities (low,high) → (low',high') ──────────────

/-- Parallel motion: both voices move the same signed amount. We model a move as
    (Δlow, Δhigh) and test equality of direction-and-distance. -/
def isParallel (dLow dHigh : Int) : Bool := dLow == dHigh && dLow ≠ 0

/-- The voice-leading law: a move is forbidden when it is parallel AND lands on a
    perfect consonance (parallel fifths / parallel octaves). -/
def forbiddenParallel (i' : Nat) (dLow dHigh : Int) : Bool :=
  isParallel dLow dHigh && isPerfect i'

/-- Parallel fifths are forbidden: two voices a fifth apart, both rising a whole
    step, arrive at another fifth in parallel — banned. -/
theorem parallel_fifths_forbidden :
    forbiddenParallel (ivl 9 2) 2 2 = true := by decide

/-- Parallel octaves are forbidden likewise. -/
theorem parallel_octaves_forbidden :
    forbiddenParallel (ivl 12 0) 2 2 = true := by decide

/-- Contrary motion INTO a fifth is allowed (voices move opposite ways). -/
theorem contrary_into_fifth_allowed :
    forbiddenParallel 7 2 (-2) = false := by decide

/-- Parallel motion through IMPERFECT consonances (e.g. parallel thirds/sixths)
    is allowed — only the perfect consonances are protected. -/
theorem parallel_thirds_allowed :
    forbiddenParallel 4 2 2 = false := by decide

end CounterpointIntervals
