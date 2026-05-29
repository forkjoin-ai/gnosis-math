/-
  SongGrandUnification.lean
  =========================

  The whole song engine in one theorem. Init-only, zero sorry. Each clause is
  proved in its own module; here they are conjoined so the single picture is
  legible at once: ONE swerve (n ↦ n+1) generates ONE structure (the walk on Z/12),
  which projects into every modality — and the projections are provably the same
  motion seen from different sides.

      atoms (swerve)  →  elements (the modalities)  →  matter (a song)
-/

import Gnosis.SongUnification
import Gnosis.HarmonicSeries
import Gnosis.EuclideanRhythm
import Gnosis.JustIntonation
import Gnosis.CounterpointIntervals
import Gnosis.MelodicSymmetry
import Gnosis.GoldenMeter
import Gnosis.ResolutionLadder

namespace SongGrandUnification

/-- The one picture: the swerve, the shared inversion, the overtone triad, the
    tritone's double dissonance, equal temperament's compromise, the maximally-even
    rhythm, the melodic mirror, and the golden bar — all at once. -/
theorem song_grand_unification :
    -- ATOM: the creative primitive is the successor swerve
    (∀ n : Nat, ResolutionLadder.upres n = n + 1) ∧
    -- harmony and poetry invert by ONE cyclic action (head → tail)
    (∀ l : List Nat, ChromaticChord.invert l = WordInversion.rotate1 l) ∧
    -- the major triad is nature's chord (overtones 4:5:6)
    (HarmonicSeries.sharedPeriod 5 4 = 20 ∧ HarmonicSeries.sharedPeriod 6 4 = 12) ∧
    -- the tritone is dissonant where the fifth is consonant (harmony = counterpoint)
    (CounterpointIntervals.isConsonant 6 = false ∧ CounterpointIntervals.isConsonant 7 = true) ∧
    -- equal temperament tempers the major third most (14¢ sharp)
    (JustIntonation.err JustIntonation.justMajorThird 4 = 14) ∧
    -- rhythm shares beats as evenly as pitch shares the octave (E(3,8) = tresillo)
    (EuclideanRhythm.beats 3 8 = 3) ∧
    -- the melodic mirror is an involution (R∘R = id) — the Klein-four symmetry
    (∀ l : List Nat, MelodicSymmetry.R (MelodicSymmetry.R l) = l) ∧
    -- the golden bar: player(5) + sky(8) = 13
    (GoldenMeter.playerBars + GoldenMeter.skyBars = GoldenMeter.barBeats) :=
  ⟨fun _ => rfl,
   SongUnification.chord_and_word_inversion_agree,
   by decide,
   by decide,
   by decide,
   by decide,
   MelodicSymmetry.retrograde_involutive,
   by decide⟩

/-- Restated as a slogan: every modality is the swerve, read in its own alphabet —
    pitch, hue, letter, beat, voice. -/
theorem one_swerve_many_alphabets :
    (∀ n : Nat, ResolutionLadder.upres n = n + 1) ∧
    (∀ l : List Nat, ChromaticChord.invert l = WordInversion.rotate1 l) :=
  ⟨fun _ => rfl, SongUnification.chord_and_word_inversion_agree⟩

end SongGrandUnification
