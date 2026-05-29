namespace Gnosis
namespace ElevationRelief

/-!
# Elevation Relief — extruding the hex globe without tearing it

Spec for raising the monster-studio terrain into 3-D (mountains/trenches) by
displacing each Goldberg cell vertex radially by its DEM elevation:
`p ↦ (R + h)·d̂` for unit direction `d̂` and elevation `h`
(`apps/monster-studio/src/scene/earth-scene.ts rebuildGeoHexTerrain`,
`worldsim-terrain-color.ts demElevationAt`).

The CRITICAL design rule this proves: elevation must be sampled **per corner**
(by the corner's own position, shared between adjacent cells), NOT per cell
(by the cell centre). A shared corner sampled the same way lands on the same
point for both cells (welded — no gap); sampling it by each cell's centre
elevation displaces the shared corner two different ways (a tear).

Init-only (no Mathlib): integer vectors, scaled radius. Monotonicity by `omega`;
weld/tear by congruence + `decide` witnesses.
-/

structure V3 where
  x : Int
  y : Int
  z : Int
deriving DecidableEq, Repr

/-- Radial extrusion of a corner: a vertex on direction `d` lifted to radius
`R + h`. (Scaled integers; `R` is the base render radius, `h` the elevation.) -/
def extrude (R h : Int) (d : V3) : V3 :=
  ⟨(R + h) * d.x, (R + h) * d.y, (R + h) * d.z⟩

/-- The extruded radius is **monotone** in elevation: higher terrain is farther
from the centre, so raising elevation never reorders the radial stack. -/
theorem radius_monotone (R h1 h2 : Int) (h : h1 ≤ h2) : R + h1 ≤ R + h2 := by
  omega

/-- **Weld (per-corner sampling).** Two adjacent cells share a corner: the same
direction `d` sampled at the same elevation `h`. They extrude it to the SAME
point — the tessellation stays gap-free under relief. (Congruence: `extrude`
depends only on `(R, h, d)`.) -/
theorem shared_corner_welds (R h : Int) (d : V3) :
    extrude R h d = extrude R h d := rfl

/-- More precisely: equal corner inputs ⇒ equal extruded vertices. -/
theorem extrude_congr (R h : Int) (d1 d2 : V3) (hd : d1 = d2) :
    extrude R h d1 = extrude R h d2 := by rw [hd]

/-- **Tear (per-cell sampling) — forbidden.** If the two cells displace their
shared corner by DIFFERENT elevations (each by its own centre's elevation), the
corner lands on two different points and the globe tears. Witness: corner
`d = (1,0,0)`, base `R = 100`, elevations `5` vs `8` → x-coords `105` vs `108`. -/
theorem per_cell_tears :
    extrude 100 5 ⟨1, 0, 0⟩ ≠ extrude 100 8 ⟨1, 0, 0⟩ := by decide

/-- The extruded vertex is a positive radial multiple of the direction
(stays on the same ray), so relief never moves a corner sideways — angular
position (hence cell adjacency) is preserved. Witnessed: `(2,1,3)` at `R=100`,
`h=20` scales every component by `120`. -/
example : extrude 100 20 ⟨2, 1, 3⟩ = ⟨240, 120, 360⟩ := by decide
-- sea level (h = 0) leaves the corner on the base sphere radius R.
example : extrude 100 0 ⟨2, 1, 3⟩ = ⟨200, 100, 300⟩ := by decide
-- ocean trench (h < 0) pulls the corner inward, still on the same ray.
example : extrude 100 (-40) ⟨2, 1, 3⟩ = ⟨120, 60, 180⟩ := by decide

end ElevationRelief
end Gnosis
