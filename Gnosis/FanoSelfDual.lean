import Init

/-
  FanoSelfDual.lean
  =================

  THE SEVEN FOLDS ON ITSELF. `SevenVectorFold` names the 7 NONZERO vectors of
  `GF(2)³ = Bool³` as the points of the Fano plane `PG(2,2)` — the barrier-sights.
  Here we add the other half of the picture and close the duality.

  A LINE of `PG(2,2)` is a linear functional on `GF(2)³`, i.e. its nonzero
  coefficient vector — again one of the same 7 nonzero `Bool³` vectors. A point
  `p` lies on a line `ℓ` exactly when the `GF(2)` dot product vanishes:
  `p·ℓ = 0`. So POINTS and LINES are drawn from the *same* 7 vectors, and the
  incidence relation is the symmetric bilinear form `dot p ℓ = 0`.

  This is the genuine `7₃` configuration of finite projective geometry:
    · 7 points, 7 lines;
    · every line carries exactly 3 points;
    · every point lies on exactly 3 lines;
    · point ↔ line is a symmetric involution — the plane is SELF-DUAL.
  The seven literally fold onto themselves: the structure SevenVectorFold's
  barrier-sights live on.

  Init only, finite, decidable. Zero `sorry`, zero new `axiom`.
-/

namespace FanoSelfDual

/-- A point of `PG(2,2)`: a nonzero `GF(2)³` vector. -/
abbrev Point := Bool × Bool × Bool

/-- A line of `PG(2,2)`: a nonzero coefficient vector (a linear functional). -/
abbrev Line := Bool × Bool × Bool

/-- `GF(2)` dot product of two `Bool³` vectors: bitwise AND, summed mod 2 (XOR). -/
def dot (p : Point) (ℓ : Line) : Bool :=
  ((p.1 && ℓ.1) != (p.2.1 && ℓ.2.1)) != (p.2.2 && ℓ.2.2)

/-- Point `p` is incident to line `ℓ` iff their `GF(2)` dot product vanishes. -/
def incident (p : Point) (ℓ : Line) : Bool := dot p ℓ == false

/-- The blind-to-everything zero vector (excluded from the plane). -/
def isZero (v : Bool × Bool × Bool) : Bool := (!v.1) && (!v.2.1) && (!v.2.2)

/-- **The seven points** — the nonzero vectors of `GF(2)³`. -/
def points : List Point :=
  [ (true,  false, false)
  , (false, true,  false)
  , (true,  true,  false)
  , (false, false, true)
  , (true,  false, true)
  , (false, true,  true)
  , (true,  true,  true) ]

/-- **The seven lines** — the SAME seven nonzero vectors, read as functionals. -/
def lines : List Line :=
  [ (true,  false, false)
  , (false, true,  false)
  , (true,  true,  false)
  , (false, false, true)
  , (true,  false, true)
  , (false, true,  true)
  , (true,  true,  true) ]

/-- There are exactly seven points. -/
theorem seven_points : points.length = 7 := by decide

/-- There are exactly seven lines. -/
theorem seven_lines : lines.length = 7 := by decide

/-- Every point is a nonzero vector. -/
theorem points_all_nonzero : ∀ p ∈ points, isZero p = false := by decide

/-- Every line is a nonzero vector. -/
theorem lines_all_nonzero : ∀ ℓ ∈ lines, isZero ℓ = false := by decide

/-- **Each line carries exactly three points.** -/
theorem each_line_has_three_points :
    ∀ ℓ ∈ lines, (points.filter (incident · ℓ)).length = 3 := by decide

/-- **Each point lies on exactly three lines.** -/
theorem each_point_on_three_lines :
    ∀ p ∈ points, (lines.filter (incident p ·)).length = 3 := by decide

/-- Incidence is symmetric: `p` on `ℓ` iff `ℓ` on `p` (the dot form is symmetric).
    This is the duality at the level of a single incidence. -/
theorem incident_symm : ∀ p ∈ points, ∀ ℓ ∈ lines, incident p ℓ = incident ℓ p := by
  decide

/-- **The Fano plane is self-dual.** Points and lines are literally the same seven
    vectors, so the `7₃` configuration — 7 points, 7 lines, 3 on each line, 3
    through each point, symmetric incidence — is sent to itself under point ↔ line.
    The seven fold onto themselves. -/
theorem self_dual : points = lines := by decide

end FanoSelfDual
