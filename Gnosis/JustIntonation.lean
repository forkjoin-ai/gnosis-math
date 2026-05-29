/-
  JustIntonation.lean
  ===================

  Why equal temperament is a compromise — and exactly where it bites. Init-only,
  zero sorry. Measured in integer CENTS (1200 to the octave; the just intervals are
  the standard integer-cent approximations of the overtone ratios of
  HarmonicSeries.lean — 702 ≈ log₂(3/2)·1200, etc.).

  Equal temperament puts every semitone at exactly 100 cents. The just (overtone)
  intervals do not land there: the perfect fifth is off by ~2 cents (inaudible),
  but the major third is off by ~14 — which is why ET thirds ring a touch sharp.
  Stacking the small errors gives the two famous commas: twelve fifths overshoot
  seven octaves by the Pythagorean comma; four fifths overshoot two octaves plus a
  third by the syntonic comma.
-/

namespace JustIntonation

/-- Equal-temperament value of n semitones, in cents. -/
def etCents (semitones : Nat) : Nat := 100 * semitones

-- Just (overtone-derived) intervals, integer cents:
def justOctave : Nat := 1200   -- 2:1
def justFifth : Nat := 702     -- 3:2
def justFourth : Nat := 498    -- 4:3
def justMajorThird : Nat := 386 -- 5:4
def justMinorThird : Nat := 316 -- 6:5

/-- Absolute tuning error (cents) between a just interval and its ET semitone slot. -/
def err (just etSemi : Nat) : Nat :=
  let et := etCents etSemi
  if just ≥ et then just - et else et - just

/-- The perfect fifth is nearly pure in ET — off by just 2 cents. -/
theorem fifth_nearly_pure : err justFifth 7 = 2 := by decide

/-- The perfect fourth is likewise nearly pure (2 cents). -/
theorem fourth_nearly_pure : err justFourth 5 = 2 := by decide

/-- The major third is ET's audible compromise — sharp by 14 cents. -/
theorem major_third_is_sharp : err justMajorThird 4 = 14 := by decide

/-- Among the common consonances, ET tempers the major third most and the
    fifth/fourth least. (This is what you hear.) -/
theorem et_compromises_the_third_most :
    err justMajorThird 4 > err justFifth 7 ∧ err justMajorThird 4 > err justFourth 5 := by
  decide

/-- The octave is exact in ET (the one interval temperament keeps pure). -/
theorem octave_is_exact : err justOctave 12 = 0 := by decide

/-- The Pythagorean comma: twelve just fifths overshoot seven octaves
    (8424 − 8400 = 24 cents — the gap the circle of fifths cannot close). -/
theorem pythagorean_comma : 12 * justFifth - 7 * justOctave = 24 := by decide

/-- The syntonic comma: four just fifths overshoot two octaves plus a just major
    third (2808 − 2786 = 22 cents — meantone's burden). -/
theorem syntonic_comma : 4 * justFifth - (2 * justOctave + justMajorThird) = 22 := by decide

/-- A just major third plus a just minor third make a just perfect fifth
    (386 + 316 = 702) — the triad stacks exactly, before temperament rounds it. -/
theorem thirds_stack_to_a_fifth : justMajorThird + justMinorThird = justFifth := by decide

end JustIntonation
