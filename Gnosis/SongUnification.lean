/-
  SongUnification.lean
  ====================

  We have the atoms; here we make the elements and build the matter. Init-only,
  zero sorry. This module imports the suite and ties it into one substance:

      ATOM     the clinamen swerve  n ↦ n+1            (ResolutionLadder.upres)
      ELEMENTS the modalities — projections of one Z/12:
                 melody  (MarkovSong),  harmony (ChromaticChord),
                 palette (ChromaticColorWheel),  word (WordInversion),
                 resolution (ResolutionLadder)
      MATTER   a Song — lyric ⊕ melody ⊕ palette grown from one tonic + swerves

  Two unifications are proved, not asserted:
    * chord inversion and word inversion are the SAME function (head→tail);
    * a melodic major-third step and a triadic colour step are the SAME +Δ —
      so the note that sounds and the hue that shows move together.
-/

import Gnosis.ChromaticChord
import Gnosis.WordInversion
import Gnosis.ChromaticColorWheel
import Gnosis.ResolutionLadder
import Gnosis.MarkovSong

namespace SongUnification

-- ── the atom ─────────────────────────────────────────────────────────────────

/-- The single creative atom — the swerve — equals the successor +1 (every element
    is built from it). -/
theorem creative_atom_eq_succ (n : Nat) : ResolutionLadder.upres n = n + 1 := rfl

-- ── unifying the elements ────────────────────────────────────────────────────

/-- Chord inversion and word inversion are one operation — send the head to the
    tail — on EVERY list. Harmony and poetry invert by the very same cyclic action
    (proved generally, not just witnessed). -/
theorem chord_and_word_inversion_agree (l : List Nat) :
    ChromaticChord.invert l = WordInversion.rotate1 l := by
  cases l <;> rfl

/-- The melody and the palette move together at every pitch: ascending a major
    third (the Markov step) advances the hue by the triadic 120°. The note you
    hear and the colour you see are the same swerve of the one Z/12. -/
theorem melody_and_palette_step_agree :
    (ChromaticColorWheel.allPC.all (fun p =>
      ChromaticColorWheel.hueOf (MarkovSong.step p)
        == (ChromaticColorWheel.hueOf p + 120) % 360)) = true := by decide

/-- The elements of creative matter — the modalities the one walk projects into.
    Mirrors aeon-poetry's `modalities` (the Rust scaffold), kept in step here. -/
def modalities : List String :=
  ["lyric", "melody", "harmony", "rhythm", "palette", "geometry"]

theorem six_elements : modalities.length = 6 := by decide

-- ── building the matter: a Song ──────────────────────────────────────────────

/-- A Song: a tonic (the atom's landing pitch), a resolution (lattice/chord
    extension), and the swerve-bits that choose its melody. Lyric, melody, palette
    and harmony are all read off these. -/
structure Song where
  tonic : Nat
  resolution : Nat
  swerves : List Bool

/-- The Song's melody: the creature's whistle from its tonic. -/
def Song.melody (s : Song) : List Nat := MarkovSong.whistle (s.tonic % 12) s.swerves

/-- The Song's harmonic body: voices in the tertian chord at its resolution. -/
def Song.voices (s : Song) : Nat := ResolutionLadder.chordVoices s.resolution

/-- The Song's colour: the hue of its tonic. -/
def Song.hue (s : Song) : Nat := ChromaticColorWheel.hueOf (s.tonic % 12)

/-- A song always sounds its tonic first and once per swerve after: a phrase of
    `swerves.length + 1` notes. Music has a definite length grown from the atoms. -/
theorem song_melody_length (s : Song) :
    s.melody.length = s.swerves.length + 1 := by
  simpa [Song.melody] using MarkovSong.whistle_length (s.tonic % 12) s.swerves

/-- Poetry ⊕ music: at the triton/haiku anchor (resolution 0) a two-swerve song
    is a three-note melody AND a three-part form — one matter, two readings. -/
theorem song_is_poetry_and_music :
    let s : Song := { tonic := 0, resolution := 0, swerves := [false, false] }
    s.melody.length = ResolutionLadder.parts 0 ∧ s.melody = [0, 4, 8] := by
  decide

/-- A worked stanza: tonic C, three swerves (M, M, m), painted red (0°),
    bodied as a triad. The whole creative atom-to-matter chain in one value. -/
theorem a_complete_song :
    let s : Song := { tonic := 0, resolution := 0, swerves := [false, false, true] }
    s.melody = [0, 4, 8, 11] ∧ s.voices = 3 ∧ s.hue = 0 := by
  decide

end SongUnification
