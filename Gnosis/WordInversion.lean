/-
  WordInversion.lean
  ==================

  Words, and inversions of words — in the spirit of e.e. cummings, who spun
  "r-p-o-p-h-e-s-s-a-g-r" until it landed as "grasshopper", and folded "a leaf
  falls" inside "l(a…)oneliness". Init-only (no Mathlib), zero sorry.

  The claim worth making precise: the inversion of a WORD and the inversion of a
  CHORD are the SAME cyclic-group action. A voicing is a list of pitch classes; a
  word is a list of letters; both invert by `rotate1` — send the head to the tail.
  ChromaticChord.invert and WordInversion.rotate1 are literally the same function
  on `List`; SongUnification.lean proves they agree.

  Conserved under every spindle is the letter MULTISET (and hence the length —
  the ropelength / Betti charge of BashoClinamenFoldingInvariant.lean): permuting
  letters reorders without creating or destroying. cummings' play is exactly this
  — rearrangement at constant charge, meaning re-found in a new order.
-/

namespace WordInversion

/-- A letter as a code (a=0 … z=25); a word is a list of letters. -/
abbrev Word := List Nat

/-- One inversion / spindle step: the first letter rotates to the end. The same
    operation that takes a chord to its next inversion. -/
def rotate1 : List α → List α
  | [] => []
  | a :: rest => rest ++ [a]

/-- Iterate the spindle `n` times. -/
def rotateN : Nat → List α → List α
  | 0, w => w
  | (n + 1), w => rotateN n (rotate1 w)

/-- Retrograde: read the word backwards (the cancrizans / mirror of music). -/
def retrograde (w : List α) : List α := w.reverse

-- ── conservation laws ────────────────────────────────────────────────────────

/-- A spindle step preserves length — letters are reordered, never lost. -/
theorem rotate_preserves_length (w : List α) :
    (rotate1 w).length = w.length := by
  cases w with
  | nil => rfl
  | cons a rest => simp [rotate1]

/-- Retrograde preserves length. -/
theorem retrograde_preserves_length (w : List α) :
    (retrograde w).length = w.length := by
  simp [retrograde]

/-- Retrograde is an involution: mirror the mirror and the word returns. -/
theorem retrograde_involutive (w : List α) :
    retrograde (retrograde w) = w := by
  simp [retrograde]

-- ── normal form for "same letters" (anagram = a valid spindle) ───────────────

def insert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys

def sort : List Nat → List Nat
  | [] => []
  | x :: xs => insert x (sort xs)

/-- "grasshopper" as letter codes. -/
def grasshopper : Word := [6, 17, 0, 18, 18, 7, 14, 15, 15, 4, 17]

/-- A spindle step of "grasshopper" is an anagram of it — same letter multiset,
    new order. cummings' grasshopper re-assembling itself. -/
theorem spindle_is_anagram :
    sort (rotate1 grasshopper) = sort grasshopper := by decide

/-- "grasshopper" has eleven letters; after eleven spindles it lands home. -/
theorem grasshopper_period_eleven :
    rotateN 11 grasshopper = grasshopper := by decide

/-- The retrograde of "grasshopper" is still an anagram of it (same charge). -/
theorem retrograde_is_anagram :
    sort (retrograde grasshopper) = sort grasshopper := by decide

-- ── words and chords share one inversion (concrete witness) ───────────────────

/-- On any list, the word-spindle and the chord-inversion rule agree by
    definition: head-to-tail. Witnessed here on a triad-shaped word. -/
theorem inversion_rule_is_uniform :
    rotate1 [0, 4, 7] = [4, 7, 0] := by decide

end WordInversion
