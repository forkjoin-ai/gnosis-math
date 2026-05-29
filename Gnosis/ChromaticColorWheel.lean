/-
  ChromaticColorWheel.lean
  ========================

  "Chromatic" carries two meanings — the twelve-tone pitch chroma and the colour
  chroma — and they are the SAME ring. Init-only (no Mathlib), zero sorry, every
  proof by `decide` over the twelve residues.

  Map each pitch class p ∈ Z/12 to a hue `hueOf p = 30·p` degrees on the colour
  wheel (twelve hues, 30° apart). This map is Z/12-equivariant: stepping one
  semitone steps 30° of hue. Hence the harmonic relations of ChromaticChord.lean
  become colour-theory relations:

    * a SEMITONE (+1)        ↔ an ANALOGOUS colour (+30°)
    * a MAJOR THIRD (+4)     ↔ a TRIADIC colour   (+120°)   — the augmented triad
                                                              = the triadic palette
                                                              = the Coltrane cycle
    * a TRITONE (+6)         ↔ a COMPLEMENTARY colour (+180°) — max harmonic AND
                                                                max visual contrast

  This is the `palette` modality of the song engine: the same swerve that writes
  the melody paints the picture (see aeon-poetry's NoiseColor / point-path).
-/

namespace ChromaticColorWheel

/-- Hue in degrees for a pitch class: twelve evenly spaced hues, 30° apart. -/
def hueOf (p : Nat) : Nat := (30 * (p % 12)) % 360

/-- The twelve pitch classes / the twelve hues. -/
def allPC : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- One semitone advances the hue by exactly 30° — the pitch ring and the colour
    wheel are one Z/12, and `hueOf` is its order-preserving 30°-scaling. -/
theorem semitone_steps_thirty_degrees :
    (allPC.all (fun p => hueOf ((p + 1) % 12) == (hueOf p + 30) % 360)) = true := by
  decide

/-- A major third (the chord's stacking interval) is the triadic colour scheme:
    three hues 120° apart. -/
theorem major_third_is_triadic_colour :
    (allPC.all (fun p => hueOf ((p + 4) % 12) == (hueOf p + 120) % 360)) = true := by
  decide

/-- A tritone is the complementary colour: +180°, the wheel's opposite point.
    Maximum harmonic dissonance ↔ maximum visual contrast. -/
theorem tritone_is_complementary_colour :
    (allPC.all (fun p => hueOf ((p + 6) % 12) == (hueOf p + 180) % 360)) = true := by
  decide

/-- A semitone is the analogous colour (neighbour on the wheel). -/
theorem semitone_is_analogous_colour :
    (allPC.all (fun p => hueOf ((p + 1) % 12) == (hueOf p + 30) % 360)) = true := by
  decide

/-- `hueOf` is injective on the twelve classes: distinct pitches → distinct hues
    (the bijection pitch-chroma ≅ colour-chroma). -/
theorem hue_injective_on_twelve :
    (allPC.all (fun a => allPC.all (fun b => (hueOf a == hueOf b) == (a == b)))) = true := by
  decide

/-- The augmented triad {0,4,8} paints the three triadic hues {0°, 120°, 240°}. -/
theorem aug_triad_is_triadic_palette :
    (hueOf 0, hueOf 4, hueOf 8) = (0, 120, 240) := by decide

/-- C and its tritone F♯ are complementary hues: red (0°) and cyan (180°). -/
theorem c_and_fsharp_are_complementary :
    hueOf 0 = 0 ∧ hueOf 6 = 180 := by decide

end ChromaticColorWheel
