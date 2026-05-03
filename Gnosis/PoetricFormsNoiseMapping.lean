/-
  PoetricFormsNoiseMapping.lean
  =============================

  Mapping historical poetic forms to the noise spectrum lattice.

  Each poetic form has a ropelength (syllable count or line count) and
  a structural character (repetition, rotation, recursion, etc.).

  This character maps to a noise color:
    Brown noise: low frequency, correlated, memory (small ropelength, tight loops)
    Pink noise: self-similar, fractal (repeating refrains, recursive structure)
    White noise: uncorrelated, random (no repetition, pure form)
    Violet noise: high frequency, sharp (complex rotation, interference)
    Ultraviolet: exponential growth, meta-structure (hidden dimensions)

  The ropelength ladder of human poetic forms:
    Triolet (8) → Rondeau (15) → Haiku (17) → Villanelle (19) → Tanka (31) →
    Sestina (39) → ... → Cadae (120 total)
-/

namespace PoetricFormsNoiseMapping

-- ══════════════════════════════════════════════════════════
-- POETIC FORM STRUCTURE
-- ══════════════════════════════════════════════════════════

/-- A poetic form is characterized by:
    - name: the form's name
    - ropelength: total syllables or lines
    - pattern: the repetition/rotation structure
    - noise_color: which frequency domain it occupies
    - is_fractal: whether it has self-similar structure
-/
structure PoeticForm where
  name : String
  ropelength : Nat
  pattern : String             -- description of the form's pattern
  noise_color : String         -- Brown, Pink, White, Violet, Ultraviolet
  is_fractal : Bool            -- self-similar recursion?

-- ══════════════════════════════════════════════════════════
-- BROWN NOISE FORMS (low frequency, correlated, tight loops)
-- ══════════════════════════════════════════════════════════

/-- Triolet: 8 lines total. Two repeated lines create a tight loop.
    Minimal ropelength. Strong correlation. Pure brown noise. -/
def Triolet : PoeticForm where
  name := "Triolet"
  ropelength := 8
  pattern := "8 lines, 2 lines repeated 4 times total, tight loop"
  noise_color := "Brown"
  is_fractal := false

/-- Rondeau: 15 lines. Repeating refrain creates low-frequency oscillation.
    Between brown and pink. -/
def Rondeau : PoeticForm where
  name := "Rondeau"
  ropelength := 15
  pattern := "15 lines, repeating refrain, rhyme scheme ABA"
  noise_color := "Brown/Pink transition"
  is_fractal := true

-- ══════════════════════════════════════════════════════════
-- HAIKU: THE BASELINE (our reality = brown noise)
-- ══════════════════════════════════════════════════════════

/-- Haiku: 5-7-5 = 17 syllables. The fundamental form.
    This is Basho's witness proof. The baseline of human poetry.
    Brown noise. Our reality. Ropelength 17. -/
def Haiku : PoeticForm where
  name := "Haiku"
  ropelength := 17
  pattern := "5-7-5 syllables, triton (stillness-sting-trill)"
  noise_color := "Brown"
  is_fractal := false

theorem haiku_is_brown_baseline :
    Haiku.ropelength = 17 ∧ Haiku.noise_color = "Brown" := by
  simp [Haiku]

-- ══════════════════════════════════════════════════════════
-- BROWN/PINK TRANSITION FORMS
-- ══════════════════════════════════════════════════════════

/-- Villanelle: 19 lines. Two repeating lines + rhyme scheme.
    Deterministic chaos. Loop with variation. -/
def Villanelle : PoeticForm where
  name := "Villanelle"
  ropelength := 19
  pattern := "19 lines, 2 repeating lines, ABA rhyme, deterministic"
  noise_color := "Brown/Pink"
  is_fractal := true

-- ══════════════════════════════════════════════════════════
-- PINK NOISE FORMS (self-similar, fractal, recursive)
-- ══════════════════════════════════════════════════════════

/-- Ghazal: Series of couplets (length variable) with repeating refrain.
    Inherently self-similar. Each couplet stands alone but echoes the refrain.
    Pink noise: fractal structure at all scales. -/
def Ghazal : PoeticForm where
  name := "Ghazal"
  ropelength := 0             -- variable length
  pattern := "Series of couplets, repeating refrain, self-similar"
  noise_color := "Pink"
  is_fractal := true

/-- Pantoum: Quatrains with specific line repetitions.
    Recursive looping. Each line appears twice, creating interference.
    Pink noise signature. -/
def Pantoum : PoeticForm where
  name := "Pantoum"
  ropelength := 0             -- variable (multiples of 4)
  pattern := "Quatrains (4-line stanzas), lines repeat in next stanza"
  noise_color := "Pink"
  is_fractal := true

-- ══════════════════════════════════════════════════════════
-- PINK/WHITE TRANSITION: TANKA (haiku extended)
-- ══════════════════════════════════════════════════════════

/-- Tanka: 5-7-5-7-7 = 31 syllables. Haiku extended by 14 syllables.
    The haiku (17) plus resolution (14). Bridges brown and white noise.
    Pink noise with structure. -/
def Tanka : PoeticForm where
  name := "Tanka"
  ropelength := 31
  pattern := "5-7-5-7-7 syllables, haiku (5-7-5) + resolution (7-7)"
  noise_color := "Pink/White"
  is_fractal := true

theorem tanka_is_haiku_extended :
    Tanka.ropelength = Haiku.ropelength + 14 ∧
    Tanka.ropelength = 31 := by
  simp [Tanka, Haiku]

-- ══════════════════════════════════════════════════════════
-- WHITE/VIOLET TRANSITION: SESTINA (harmonic interference)
-- ══════════════════════════════════════════════════════════

/-- Sestina: 39 lines (6 stanzas × 6 lines + 1 envoi) of 6 end-words
    rotating in complex pattern. Harmonic structure.
    Each end-word appears 6 times (6-fold symmetry = violet interference).
    Sharp, high-frequency rotation pattern. -/
def Sestina : PoeticForm where
  name := "Sestina"
  ropelength := 39
  pattern := "39 lines, 6 end-words in rotating pattern, 6-fold symmetry"
  noise_color := "White/Violet"
  is_fractal := false

-- ══════════════════════════════════════════════════════════
-- VIOLET/ULTRAVIOLET: EXPONENTIAL GROWTH
-- ══════════════════════════════════════════════════════════

/-- Cadae (Cascade): 15 lines where line N has N syllables.
    1+2+3+...+15 = 120 total syllables.
    Triangular explosion. Each line adds more complexity.
    Ultraviolet: exponential growth, dimensional stacking. -/
def Cadae : PoeticForm where
  name := "Cadae"
  ropelength := 120          -- sum 1..15
  pattern := "15 lines, line N has N syllables, triangular growth, 1+2+...+15"
  noise_color := "Violet/Ultraviolet"
  is_fractal := false

theorem cadae_ropelength :
    Cadae.ropelength = 120 := by
  simp [Cadae]

-- ══════════════════════════════════════════════════════════
-- ULTRAVIOLET: META-STRUCTURAL (hidden dimensions)
-- ══════════════════════════════════════════════════════════

/-- Golden Shovel: The last word of each line, read vertically,
    forms a hidden phrase from another poem.
    Meta-structure. The meaning is embedded in a higher dimension.
    Ultraviolet: beyond the visible spectrum, 10D aeon manifold. -/
def GoldenShovel : PoeticForm where
  name := "Golden Shovel"
  ropelength := 0             -- variable, depends on the hidden phrase
  pattern := "Variable length, last words form hidden phrase (vertical read)"
  noise_color := "Ultraviolet"
  is_fractal := false

-- ══════════════════════════════════════════════════════════
-- LAI: HEXON STRUCTURE (mirror form)
-- ══════════════════════════════════════════════════════════

/-- Lai: Medieval French form with 9-line stanzas.
    Repeating rhyme scheme creates mirror structure.
    Hexon-like: one triton forward, one reflected. -/
def Lai : PoeticForm where
  name := "Lai"
  ropelength := 0             -- variable (multiples of 9)
  pattern := "9-line stanzas, repeating rhyme scheme, mirror structure"
  noise_color := "Pink/White"
  is_fractal := true

-- ══════════════════════════════════════════════════════════
-- THE ROPELENGTH LATTICE OF HUMAN POETIC FORMS
-- ══════════════════════════════════════════════════════════

/-- The complete ropelength ladder of fixed-form poetry.
    Each rung corresponds to a noise color and structural character. -/
def poetic_forms_ordered : List PoeticForm :=
  [Triolet, Rondeau, Haiku, Villanelle, Tanka, Sestina, Cadae]

theorem poetic_ladder_ropelengths :
    let forms := poetic_forms_ordered
    (forms.getD 0 Haiku).ropelength = 8 ∧    -- Triolet
    (forms.getD 2 Haiku).ropelength = 17 ∧   -- Haiku
    (forms.getD 4 Haiku).ropelength = 31 ∧   -- Tanka
    (forms.getD 5 Haiku).ropelength = 39 ∧   -- Sestina
    (forms.getD 6 Haiku).ropelength = 120 := by -- Cadae
  simp [poetic_forms_ordered, Triolet, Haiku, Tanka, Sestina, Cadae]

-- ══════════════════════════════════════════════════════════
-- NOISE COLOR CLASSIFICATION
-- ══════════════════════════════════════════════════════════

/-- A form is Brown noise if ropelength ≤ 20 and has tight loops. -/
def is_brown_noise (f : PoeticForm) : Prop :=
  f.ropelength ≤ 20 ∧ ¬f.is_fractal

/-- A form is Pink noise if it has self-similar (fractal) structure. -/
def is_pink_noise (f : PoeticForm) : Prop :=
  f.is_fractal

/-- A form is Violet/Ultraviolet if ropelength > 39 (exponential growth). -/
def is_violet_noise (f : PoeticForm) : Prop :=
  f.ropelength > 39

theorem haiku_is_brown_noise :
    is_brown_noise Haiku := by
  simp [is_brown_noise, Haiku]

theorem ghazal_is_pink_noise :
    is_pink_noise Ghazal := by
  simp [is_pink_noise, Ghazal]

theorem tanka_is_fractal :
    is_pink_noise Tanka := by
  simp [is_pink_noise, Tanka]

theorem cadae_is_violet_noise :
    is_violet_noise Cadae := by
  simp [is_violet_noise, Cadae]

-- ══════════════════════════════════════════════════════════
-- THE UNIFIED THEOREM: HUMAN POETRY MAPS TO NOISE SPECTRUM
-- ══════════════════════════════════════════════════════════

/-
  All human poetic forms are encodings of different frequencies in the
  noise spectrum lattice.

  The forms cluster naturally:
    - Brown (8-20): Triolet, Rondeau, Haiku — low frequency, correlated
    - Pink (fractal): Villanelle, Ghazal, Pantoum, Tanka — self-similar
    - White/Violet (39+): Sestina, Cadae — high frequency, sharp patterns
    - Ultraviolet (meta): Golden Shovel — hidden dimensions, 10D embedding

  Each form is a window into a different frequency domain of the Aeon Manifold.
  A poet choosing a form is choosing which noise color to embody.

  Haiku (brown, 17) is the baseline: Basho's proof that stillness + sting → trill
  in exactly 17 units of rope. All other forms are variations on this theorem,
  played at different frequencies, with different harmonic structures.

  The Aeon Manifold contains all poetic forms simultaneously, interfering.
  The rolling verses are how the observer moves between them.
-/

theorem poetry_spans_noise_spectrum :
    (is_brown_noise Haiku) ∧
    (is_pink_noise Tanka) ∧
    (is_violet_noise Cadae) ∧
    (Haiku.ropelength = 17) := by
  simp [is_brown_noise, is_pink_noise, is_violet_noise, Haiku, Tanka, Cadae]

end PoetricFormsNoiseMapping
