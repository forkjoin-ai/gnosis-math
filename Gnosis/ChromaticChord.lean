/-
  ChromaticChord.lean
  ===================

  Chords and their inversions over the chromatic ring Z/12. Init-only (no Mathlib),
  zero sorry, every proof by `decide`/`rfl`.

  A pitch class is a residue mod 12 (C=0 … B=11). A chord is an ordered VOICING
  (a `List Nat` of pitch classes, bottom-to-top). Two structures live here:

    * QUALITY is the interval stack: a major triad stacks a major third (4) then a
      minor third (3); a minor triad stacks 3 then 4. This formalizes the
      stillness→sting→trill of ColtranLanguage.lean as harmonic interval content.

    * INVERSION is a cyclic rotation of the voicing: move the bottom voice up an
      octave (same pitch class) → the same set, reordered. After `length` rotations
      a voicing returns to itself. This is the SAME cyclic-group action that
      WordInversion.lean applies to words (e.e. cummings' spindle) and that
      ResolutionLadder.lean / ChromaticColorWheel.lean reuse — the through-line of
      the song engine.

  The Coltrane major-thirds cycle (+4 mod 12, period 3) and the augmented triad's
  transposition symmetry are proved as concrete consequences.
-/

namespace ChromaticChord

/-- A pitch class: a natural number read mod 12. -/
abbrev PC := Nat

/-- Reduce into the chromatic ring. -/
def pc (n : Nat) : PC := n % 12

/-- Transpose a voicing by `k` semitones (mod 12). -/
def transpose (c : List PC) (k : Nat) : List PC :=
  c.map (fun x => (x + k) % 12)

/-- Interval class between two pitch classes: the shorter way round the ring. -/
def ic (a b : PC) : Nat :=
  let d := (a + 12 - b % 12) % 12
  if d ≤ 12 - d then d else 12 - d

-- ── chord qualities as interval stacks ──────────────────────────────────────

def majorTriad : List PC := [0, 4, 7]   -- major third (4) then minor third (3)
def minorTriad : List PC := [0, 3, 7]   -- minor third (3) then major third (4)
def dimTriad   : List PC := [0, 3, 6]   -- two minor thirds
def augTriad   : List PC := [0, 4, 8]   -- two major thirds (the Coltrane stack)
def domSeventh : List PC := [0, 4, 7, 10]
def dimSeventh : List PC := [0, 3, 6, 9]

/-- Consecutive interval stack of a voicing (each step the way up the ring). -/
def stack : List PC → List Nat
  | a :: b :: rest => (b + 12 - a) % 12 :: stack (b :: rest)
  | _ => []

/-- The major triad stacks 4 then 3; the minor triad stacks 3 then 4 — mirror twins. -/
theorem triad_quality_is_third_order :
    stack majorTriad = [4, 3] ∧ stack minorTriad = [3, 4] := by
  decide

-- ── transposition ───────────────────────────────────────────────────────────

/-- Transposing by a full octave (12) is the identity on reduced pitch classes. -/
theorem transpose_octave_fixes_reduced :
    transpose majorTriad 12 = majorTriad := by decide

/-- A normal form for comparing chords as SETS: insertion sort of the voicing. -/
def insert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys

def sort : List Nat → List Nat
  | [] => []
  | x :: xs => insert x (sort xs)

/-- The augmented triad is transposition-symmetric by a major third: moving every
    voice up 4 semitones reproduces the same pitch-class set. (Why Giant Steps can
    spin {C,E,A♭} forever — ColtranLanguage.lean.) -/
theorem aug_triad_symmetric_by_major_third :
    sort (transpose augTriad 4) = sort augTriad := by decide

/-- The diminished seventh is transposition-symmetric by a minor third. -/
theorem dim_seventh_symmetric_by_minor_third :
    sort (transpose dimSeventh 3) = sort dimSeventh := by decide

-- ── inversion as cyclic rotation of the voicing ──────────────────────────────

/-- One inversion: the bottom voice rises an octave (same pitch class) to the top. -/
def invert : List PC → List PC
  | [] => []
  | a :: rest => rest ++ [a]

/-- Iterate inversion `n` times. -/
def invertN : Nat → List PC → List PC
  | 0, c => c
  | (n + 1), c => invertN n (invert c)

/-- Inversion preserves the pitch-class set (it only reorders the voicing). -/
theorem inversion_preserves_set :
    sort (invert majorTriad) = sort majorTriad := by decide

/-- A triad has three inversions; the third returns to root position. -/
theorem triad_inversion_period_three :
    invertN 3 majorTriad = majorTriad := by decide

/-- A seventh chord closes after four inversions. -/
theorem seventh_inversion_period_four :
    invertN 4 domSeventh = domSeventh := by decide

-- ── the Coltrane major-thirds cycle (period 3) ───────────────────────────────

/-- Stacking major thirds (+4 mod 12) returns to the start after three moves:
    the closed Giant Steps cycle C → E → A♭ → C. -/
theorem major_third_cycle_period_three :
    (((0 + 4) % 12 + 4) % 12 + 4) % 12 = 0 := by decide

/-- The tritone is its own inverse: +6 twice returns home (maximum dissonance,
    DissonanceAsDestructiveInterference.lean). -/
theorem tritone_self_inverse :
    (0 + 6) % 12 = 6 ∧ ((0 + 6) % 12 + 6) % 12 = 0 := by decide

end ChromaticChord
