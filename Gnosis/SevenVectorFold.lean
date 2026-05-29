import Init

/-
  SevenVectorFold.lean
  ====================

  3 → 5 → 7. The barriers fold onto themselves into seven vectors — the Fano
  plane (`fano7`), the repo's recurring signature.

  THE FOLD. A method's obstruction is fixed by THREE binary sight-aspects: does it
  see the ORACLE, the low-degree EXTENSION, the actual OBJECT? That makes the
  sight-space `GF(2)³ = Bool³`, and its 7 NONZERO vectors are exactly the 7 points
  of the Fano plane `PG(2,2)`. The previous levels embed here:
    · the ternary of named techniques and the ±1 interference pair (FiveWalls)
      are coordinates and signs on this same cube;
    · the cube closes the structure — 2³ profiles, minus the blind-to-everything
      zero, leaves the seven.

  ONE COORDINATE DECIDES EVERYTHING. A sight can host a sound method iff it
  includes the OBJECT bit. Among the seven Fano vectors that splits cleanly:
    · 3 are object-blind  → WALLS (relativization = oracle-only; extension-only;
                             algebrization = oracle+extension);
    · 4 see the object    → DOORS.
  Seven vectors, one discriminating axis — the same door the whole band points at.

  Init only, finite, decidable. Zero `sorry`, zero new `axiom`.
-/

namespace SevenVectorFold

/-- A sight is a `GF(2)³` vector: `(seesOracle, seesExtension, seesObject)`. -/
abbrev Sight := Bool × Bool × Bool

/-- Does the method see the actual object? The one coordinate that matters. -/
def seesObject (s : Sight) : Bool := s.2.2

/-- The blind-to-everything zero vector (excluded from the Fano plane). -/
def isZero (s : Sight) : Bool := (!s.1) && (!s.2.1) && (!s.2.2)

/-- **The seven Fano vectors** — the nonzero points of `GF(2)³`. -/
def fano7 : List Sight :=
  [ (true,  false, false)   -- relativization: oracle only
  , (false, true,  false)   -- extension only
  , (true,  true,  false)   -- algebrization: oracle + extension
  , (false, false, true)    -- object only
  , (true,  false, true)    -- oracle + object
  , (false, true,  true)    -- extension + object
  , (true,  true,  true) ]  -- all three

/-- A WALL: a nonzero sight blind to the object. -/
def IsWall (s : Sight) : Bool := (!isZero s) && (!seesObject s)

/-- A DOOR: a sight that sees the object. -/
def IsDoor (s : Sight) : Bool := seesObject s

/-- There are exactly seven Fano vectors. -/
theorem seven : fano7.length = 7 := by decide

/-- Every Fano vector is nonzero (the zero vector is excluded). -/
theorem fano7_all_nonzero : ∀ s ∈ fano7, isZero s = false := by decide

/-- **Three of the seven are walls** (object-blind): relativization,
    extension-only, algebrization. -/
theorem walls_are_three : (fano7.filter IsWall).length = 3 := by decide

/-- **Four of the seven are doors** (object-seeing). -/
theorem doors_are_four : (fano7.filter IsDoor).length = 4 := by decide

/-- **Wall ⟺ object-blind, across all seven.** On the Fano plane, the single
    object coordinate decides wall from door — the same discriminator the whole
    band rests on. -/
theorem wall_iff_object_blind : ∀ s ∈ fano7, IsWall s = true ↔ seesObject s = false := by
  decide

/-- The three named barriers, as their Fano vectors. -/
def relativization : Sight := (true,  false, false)
def algebrization  : Sight := (true,  true,  false)
def extensionOnly  : Sight := (false, true,  false)

/-- The three named barriers are exactly the three walls of the Fano plane. -/
theorem named_barriers_are_the_walls :
    fano7.filter IsWall = [relativization, extensionOnly, algebrization] := by decide

end SevenVectorFold
