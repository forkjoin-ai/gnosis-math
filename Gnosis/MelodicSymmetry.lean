/-
  MelodicSymmetry.lean
  ====================

  The four classical transformations of a melodic line — Prime (P), Retrograde
  (R), Inversion (I), Retrograde-Inversion (RI) — and the fact that they form the
  Klein four-group V ≅ Z/2 × Z/2. Init-only, zero sorry.

  Here "inversion" means SERIAL inversion: reflect each pitch about an axis
  (p ↦ −p mod 12). This is a REFLECTION, distinct from the chord-voicing rotation
  of ChromaticChord.invert — two different symmetries, both living on Z/12.

  The point of unity: RETROGRADE is reversal — the very same reflection that
  WordInversion.retrograde applies to a word (read it backwards). So the symmetry
  group of a melody and the symmetry group of a line of verse are the same group
  acting on the same kind of list. Music and poetry share their symmetries.
-/

namespace MelodicSymmetry

/-- Serial pitch inversion about 0: p ↦ (12 − p) mod 12. -/
def inv (p : Nat) : Nat := (12 - p % 12) % 12

def allPC : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- Pitch inversion is an involution on the twelve classes (reflect twice = rest). -/
theorem inv_involutive_pointwise :
    (allPC.all (fun p => inv (inv p) == p)) = true := by decide

-- ── the four transformations of a line ───────────────────────────────────────

/-- Prime: the line as written. -/
def P (l : List Nat) : List Nat := l
/-- Retrograde: the line backwards (the cancrizans) — reversal. -/
def R (l : List Nat) : List Nat := l.reverse
/-- Inversion: every pitch reflected about the axis. -/
def I (l : List Nat) : List Nat := l.map inv
/-- Retrograde-inversion: reflect, then read backwards. -/
def RI (l : List Nat) : List Nat := (l.map inv).reverse

/-- Retrograde is an involution on ANY line — mirror the mirror, the line returns.
    (The same law as WordInversion.retrograde_involutive on words.) -/
theorem retrograde_involutive (l : List Nat) : R (R l) = l := by
  simp [R]

/-- A concrete twelve-tone row to witness the group structure. -/
def row : List Nat := [0, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9, 11]

/-- The four transforms close into the Klein four-group V = Z/2 × Z/2:
    each is an involution, and composing any two distinct non-identity transforms
    gives the third. (Here: R∘R = P, I∘I = P, RI∘RI = P, and R∘I = I∘R = RI.) -/
theorem klein_four_group :
    R (R row) = P row ∧
    I (I row) = P row ∧
    RI (RI row) = P row ∧
    R (I row) = RI row ∧
    I (R row) = RI row := by
  decide

/-- Retrograde-inversion is the composite of the two generators, in either order
    (the generators commute — V is abelian). -/
theorem ri_is_composite :
    RI row = R (I row) ∧ RI row = I (R row) := by decide

/-- A melody and its retrograde have the same length — the reflection conserves
    duration, as a word's retrograde conserves its letters. -/
theorem retrograde_preserves_length (l : List Nat) : (R l).length = l.length := by
  simp [R]

end MelodicSymmetry
