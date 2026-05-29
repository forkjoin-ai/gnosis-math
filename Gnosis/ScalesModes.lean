/-
  ScalesModes.lean
  ================

  Scales as step-patterns on Z/12, and the seven modes as ROTATIONS of one
  pattern — the same cyclic action that inverts chords and spins cummings' words
  (ChromaticChord.lean, WordInversion.lean). Init-only, zero sorry.

  The diatonic step pattern is T-T-s-T-T-T-s = [2,2,1,2,2,2,1], which sums to the
  octave (12). Rotating it once gives Dorian, again Phrygian, … and after seven
  rotations it closes back to Ionian — the modes are one necklace, read from
  seven starting beads. Cumulating the steps from a root recovers the actual
  pitch-class scale, which returns to the tonic an octave up.
-/

namespace ScalesModes

/-- The Ionian (major) step pattern: tone, tone, semitone, tone, tone, tone, semitone. -/
def ionianSteps : List Nat := [2, 2, 1, 2, 2, 2, 1]

/-- One mode rotation: the first step wraps to the end (start the necklace later). -/
def rotate1 : List Nat → List Nat
  | [] => []
  | a :: r => r ++ [a]

def rotateN : Nat → List Nat → List Nat
  | 0, l => l
  | (n + 1), l => rotateN n (rotate1 l)

/-- Every diatonic mode spans exactly one octave: the steps sum to 12. -/
theorem steps_sum_to_octave : ionianSteps.foldl (· + ·) 0 = 12 := by decide

/-- Dorian is Ionian rotated once. -/
theorem dorian_is_first_rotation :
    rotateN 1 ionianSteps = [2, 1, 2, 2, 2, 1, 2] := by decide

/-- Phrygian is Ionian rotated twice (the dark mode: semitone first). -/
theorem phrygian_is_second_rotation :
    rotateN 2 ionianSteps = [1, 2, 2, 2, 1, 2, 2] := by decide

/-- Seven modes, one necklace: after seven rotations Ionian returns. -/
theorem seven_modes_close : rotateN 7 ionianSteps = ionianSteps := by decide

/-- Cumulate steps from a root into pitch classes (mod 12). -/
def scan (acc : Nat) : List Nat → List Nat
  | [] => []
  | s :: rest => let n := (acc + s) % 12; n :: scan n rest

/-- The scale rooted at `root` with the given step pattern (tonic first). -/
def scaleFrom (root : Nat) (steps : List Nat) : List Nat :=
  root :: scan root steps

/-- C major is {C D E F G A B} and closes on the octave C. -/
theorem c_major_scale :
    scaleFrom 0 ionianSteps = [0, 2, 4, 5, 7, 9, 11, 0] := by decide

/-- A major is the same shape transposed: it begins on A (9) and returns to A. -/
theorem a_major_returns_to_tonic :
    scaleFrom 9 ionianSteps = [9, 11, 1, 2, 4, 6, 8, 9] := by decide

/-- The pentatonic scale {C D E G A} as its own step necklace [2,2,3,2,3]. -/
theorem pentatonic_steps_sum_to_octave :
    [2, 2, 3, 2, 3].foldl (· + ·) 0 = 12 := by decide

end ScalesModes
