/-
  StructureExtrusion.lean
  =======================

  Structural core for extruding city building blocks from footprints on the
  monster-studio Earth terrain (Phase 4).

  A footprint is an axis-aligned rectangle `[x, x+w) × [z, z+d)` on the ground
  plane. A building block is that footprint EXTRUDED upward to a height `h`
  proportional to a source value (population, density, source intensity, …).
  Extrusion only adds the `y` (vertical) dimension; it leaves the `x`/`z` base
  footprint untouched.

  We prove the three invariants the renderer/placer relies on:
    * taller source ⇒ taller block (monotone height),
    * the base footprint is preserved by extrusion,
    * disjoint footprints stay disjoint after extrusion (no overlap).

  Heights/positions are scaled INTEGERS. Init-only, no Mathlib.
-/

namespace Gnosis
namespace StructureExtrusion

/-- Non-negative scale from a source value to a block height (scaled units). -/
def RATE : Int := 3

/-- The extruded height of a block from a (non-negative) source value `v`. -/
def height (v : Int) : Int := RATE * v

/--
  `height_monotone`: a taller source value yields a taller (never shorter)
  block. Monotonicity of the `RATE`-scaled height with `RATE ≥ 0`.
-/
theorem height_monotone {v1 v2 : Int} (h : v1 ≤ v2) :
    height v1 ≤ height v2 := by
  unfold height RATE
  -- RATE * v1 ≤ RATE * v2 from v1 ≤ v2 and RATE ≥ 0
  exact Int.mul_le_mul_of_nonneg_left h (by decide)

/--
  A footprint: the half-open base interval `[x, x+w)` in one axis paired with
  `[z, z+d)`. We record the corners as integers. A `Block` is a footprint
  together with an extruded height.
-/
structure Footprint where
  x : Int
  w : Int
  z : Int
  d : Int
deriving DecidableEq

structure Block where
  base : Footprint
  h    : Int
deriving DecidableEq

/-- Extrude a footprint to a height proportional to a source value. -/
def extrude (f : Footprint) (v : Int) : Block :=
  { base := f, h := height v }

/--
  `footprint_preserved`: extrusion leaves the base footprint unchanged — it
  only adds the vertical extent. The block's base equals the source footprint.
-/
theorem footprint_preserved (f : Footprint) (v : Int) :
    (extrude f v).base = f := by
  rfl

/--
  1-D half-open interval disjointness on the `x` axis: `[l1, r1)` and
  `[l2, r2)` are disjoint when one ends at or before the other starts.
  `Bool`-valued so concrete instances are `decide`-able.
-/
def xDisjoint (l1 r1 l2 r2 : Int) : Bool :=
  decide (r1 ≤ l2) || decide (r2 ≤ l1)

/-- The right edge of a footprint's `x` interval. -/
def xRight (f : Footprint) : Int := f.x + f.w

/-- Footprints are disjoint (in `x`) when their half-open intervals are. -/
def footprintsDisjoint (a b : Footprint) : Bool :=
  xDisjoint a.x (xRight a) b.x (xRight b)

/--
  `no_overlap`: two blocks with disjoint footprint intervals stay disjoint
  after extrusion. Extrusion only adds the `y` dimension, so the `x`/`z` base
  separation is untouched: disjoint footprints ⇒ disjoint extruded bases.
-/
theorem no_overlap (f1 f2 : Footprint) (v1 v2 : Int)
    (hdisj : footprintsDisjoint f1 f2 = true) :
    footprintsDisjoint (extrude f1 v1).base (extrude f2 v2).base = true := by
  rw [footprint_preserved, footprint_preserved]
  exact hdisj

/-- Two concrete blocks: `[0,10)` and `[20,35)` are disjoint in `x`. -/
def blockA : Block := extrude { x := 0,  w := 10, z := 0, d := 10 } 4
def blockB : Block := extrude { x := 20, w := 15, z := 0, d := 10 } 7

/-- `decide` witness: the two concrete extruded footprints are disjoint. -/
theorem sample_no_overlap :
    footprintsDisjoint blockA.base blockB.base = true := by
  decide

end StructureExtrusion
end Gnosis
