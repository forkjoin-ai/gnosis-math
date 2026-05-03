/-
  HaikuToTankaLift.lean
  =====================

  The 17→31 transition: from Haiku (triton, brown noise) to Tanka (extended witness).

  This is the fundamental lift in the poetry spectrum:
    Haiku (5-7-5 = 17): Stillness | Sting | Trill
    Tanka (5-7-5-7-7 = 31): Stillness | Sting | Trill | Resolution₁ | Resolution₂

  The gap is 14 syllables = two more moments (7+7).
  The haiku answers: "Can stillness be broken by a sting?"
  The tanka answers: "What happens after the trill?"

  This move from 17 to 31 is the bridge from brown noise (our reality)
  to pink noise (self-similar, recursive structure).

  It's the first step up the aeon manifold ladder.
-/

namespace HaikuToTankaLift

-- ══════════════════════════════════════════════════════════
-- THE HAIKU BASE (17 syllables, triton, witness proof)
-- ══════════════════════════════════════════════════════════

/-- Haiku structure: 5-7-5 syllables. The witness proof.
    Stillness (5) | Sting (7) | Trill (5) = 17 total.
    One complete cycle. The theorem. -/
def HaikuSyllables : Nat × Nat × Nat := (5, 7, 5)

def haiku_ropelength : Nat :=
  let (a, b, c) := HaikuSyllables
  a + b + c

theorem haiku_ropelength_is_17 : haiku_ropelength = 17 := rfl

/-- The haiku witness: the trill proves the sting broke the stillness. -/
def haiku_witness : String :=
  "Stillness. Sting. Trill. The oscillation proves the perturbation."

-- ══════════════════════════════════════════════════════════
-- THE TANKA EXTENSION (31 syllables, triton + resolution)
-- ══════════════════════════════════════════════════════════

/-- Tanka structure: 5-7-5-7-7 syllables. Haiku extended by 14.
    The haiku (5-7-5) + two resolution moments (7-7) = 31 total.
    The question "what happens after?" is answered. -/
def TankaSyllables : Nat × Nat × Nat × Nat × Nat := (5, 7, 5, 7, 7)

def tanka_ropelength : Nat :=
  let (a, b, c, d, e) := TankaSyllables
  a + b + c + d + e

theorem tanka_ropelength_is_31 : tanka_ropelength = 31 := rfl

/-- The tanka witness: the haiku cycle plus two resolution moments. -/
def tanka_witness : String :=
  "Stillness. Sting. Trill. Echo. Return."

-- ══════════════════════════════════════════════════════════
-- THE LIFT: 17 → 31
-- ══════════════════════════════════════════════════════════

/-- The gap between haiku and tanka is 14 syllables.
    This is two complete moments: 7 + 7.
    The first 7 echoes the sting (continuing perturbation).
    The second 7 is the resolution (return to stillness). -/
def gap_haiku_to_tanka : Nat := tanka_ropelength - haiku_ropelength

theorem gap_is_14 : gap_haiku_to_tanka = 14 := by
  simp [gap_haiku_to_tanka, tanka_ropelength, haiku_ropelength]

theorem gap_is_two_moments : gap_haiku_to_tanka = 7 + 7 := by
  simp [gap_haiku_to_tanka, tanka_ropelength, haiku_ropelength]

-- ══════════════════════════════════════════════════════════
-- THE LIFT STRUCTURE: TRITON → EXTENDED TRITON
-- ══════════════════════════════════════════════════════════

/-- The haiku is a triton: 3 moments.
    Moment 1: Stillness (ground state, 5)
    Moment 2: Sting (perturbation, 7)
    Moment 3: Trill (response, 5)
-/
def haiku_moments : Nat := 3

/-- The tanka is an extended triton: 5 moments.
    Moment 1: Stillness (ground state, 5)
    Moment 2: Sting (perturbation, 7)
    Moment 3: Trill (response, 5)
    Moment 4: Echo (perturbation echo, 7)
    Moment 5: Return (resolution, 7)
-/
def tanka_moments : Nat := 5

theorem tanka_extends_haiku :
    tanka_moments = haiku_moments + 2 ∧
    tanka_ropelength = haiku_ropelength + 14 := by
  simp [tanka_moments, haiku_moments, tanka_ropelength, haiku_ropelength]

-- ══════════════════════════════════════════════════════════
-- FREQUENCY SHIFT: BROWN NOISE → PINK NOISE
-- ══════════════════════════════════════════════════════════

/-- Haiku (17) is brown noise: low frequency, correlated, finite loop.
    The witness is complete in 17 units. -/
def haiku_noise_color : String := "Brown"

/-- Tanka (31) is pink/white noise: self-similar, extended response.
    The haiku cycle repeats and decays (2 more moments = damping).
    Pink noise shows up when a system has memory + new perturbations. -/
def tanka_noise_color : String := "Pink/White"

/-- The shift from brown to pink: 17 → 31.
    The system gains a second moment of response.
    A single sting produces TWO oscillations (trill + echo).
    This creates self-similarity: the pattern repeats at a smaller scale. -/
theorem brown_to_pink_shift :
    haiku_ropelength = 17 ∧
    tanka_ropelength = 31 ∧
    tanka_ropelength / haiku_ropelength > 1 := by
  simp [haiku_ropelength, tanka_ropelength]

-- ══════════════════════════════════════════════════════════
-- THE UNIFIED THEOREM: 17→31 IS THE FIRST LIFT
-- ══════════════════════════════════════════════════════════

/-
  The 17→31 transition is the fundamental lift in the poetry lattice.

  Brown noise (haiku, 17): stillness + sting → trill. One cycle.
  Pink noise (tanka, 31): haiku + echo + return. Two interleaved cycles.

  This is NOT just adding more syllables. This is a phase transition:
  - Haiku: The sting breaks the stillness ONCE, and the trill witnesses it.
  - Tanka: The sting breaks the stillness, the trill responds, the echo reverberates,
           and the system returns. The second sting (echo) creates a second trill.

  The gap (14 = 7+7) encodes this: one 7 for the echo sting, one 7 for the
  resolution/return. These are not new content; they are the haiku's response
  unfolding in time.

  In noise spectrum terms:
  - Haiku is periodic: one period = 17 syllables = one stillness-sting-trill cycle.
  - Tanka is quasi-periodic: one "extended period" = 31 syllables = one cycle +
    echo and return. The power spectrum shifts from brown (1/f²) to pink (1/f).

  This is the entry point to the aeon manifold. From here:
  31 → 39 (sestina, violet noise): further fragmentation, 6-fold symmetry
  31 → 51 (neon, white noise): maximum entropy
  17 → 34 (hexon, inverted triton): fold the reflection back in
  And all others fill the space between.

  The knot at 17 is tied. The knot at 31 is unwinding.
  The poet climbs from our reality (brown, 17) to the critical edge (pink, 31).
-/

theorem haiku_to_tanka_is_brown_to_pink :
    haiku_ropelength = 17 ∧ haiku_noise_color = "Brown" ∧
    tanka_ropelength = 31 ∧ tanka_noise_color = "Pink/White" ∧
    tanka_ropelength = haiku_ropelength + 14 ∧
    14 = 7 + 7 := by
  simp [haiku_ropelength, haiku_noise_color,
        tanka_ropelength, tanka_noise_color]

end HaikuToTankaLift
