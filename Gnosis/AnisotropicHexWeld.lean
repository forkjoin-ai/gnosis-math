namespace Gnosis
namespace AnisotropicHexWeld

/-!
# Anisotropic Hex Plate Tessellation Weld

Formal contract for the monster-studio earth terrain hex plates
(`apps/monster-studio/src/scene/earth-scene.ts :: rebuildTileMeshes`).

The lat/lon ring grid has ~square cells, while a REGULAR hexagon needs an
east/north aspect ratio of √3 / 1.5 ≈ 1.155 to tile. Forcing a regular hexagon
onto square cells leaves seam "diamonds"; the renderer instead builds an
ANISOTROPIC pointy-top plate keyed to the exact grid pitch:

* east pitch  `dE` — distance between same-row cell centres,
* north pitch `dN` — distance between rows,
* odd rows are shifted half a column (`dE/2`) east — the "seesaw".

A plate centred at the origin has six vertices (in (east, north) tangent
coordinates):

```
        top = (0, +2dN/3)
  shoulderUL (-dE/2,+dN/3)   shoulderUR (+dE/2,+dN/3)
  shoulderLL (-dE/2,-dN/3)   shoulderLR (+dE/2,-dN/3)
       bottom = (0, -2dN/3)
```

To stay rational-free we scale the pitch to integers: write `dE = 2*a` and
`dN = 3*b`, so every vertex is an integer point. This is WLOG — the renderer's
continuous `dE, dN` are these integers up to a common positive scale, and the
weld identities below are scale-invariant.

The theorems prove the tessellation is EXACT — shared edges, no gap, no overlap.
Any overlap "fudge" factor (k ≠ 1) moves a shoulder off the neighbour's vertex,
which is exactly the observed "seesaw off horizontally" misalignment
(`fudge_breaks_weld_example`).

Mirrors the executable proof tests in
`open-source/aeon-3d/src/earth-orientation.test.ts`.
-/

/-- A 2D lattice point in (east, north) tangent coordinates. -/
structure Pt where
  e : Int
  n : Int
deriving DecidableEq, Repr

/-- Translation (place a plate-local vertex at a neighbour's centre). -/
def Pt.add (p q : Pt) : Pt := ⟨p.e + q.e, p.n + q.n⟩

/-- Plate-local vertices, parameterised by the half-pitches `a = dE/2`,
`b = dN/3`. All integers; no fractions. -/
def top        (b : Int) : Pt := ⟨0, 2*b⟩
def shoulderUR (a b : Int) : Pt := ⟨a, b⟩
def shoulderLR (a b : Int) : Pt := ⟨a, -b⟩
def bottom     (b : Int) : Pt := ⟨0, -2*b⟩
def shoulderLL (a b : Int) : Pt := ⟨-a, -b⟩
def shoulderUL (a b : Int) : Pt := ⟨-a, b⟩

/-- The six vertices in order, as a ring (for the area proof). -/
def ring (a b : Int) : List Pt :=
  [top b, shoulderUL a b, shoulderLL a b, bottom b, shoulderLR a b, shoulderUR a b]

/-- Neighbour centres relative to a plate at the origin, given pitch `dE = 2a`,
`dN = 3b`. Up-right / up-left are the half-shifted rows above; same-row is the
abutting cell to the east. -/
def upRight (a b : Int) : Pt := ⟨a, 3*b⟩
def upLeft  (a b : Int) : Pt := ⟨-a, 3*b⟩
def sameRow (a : Int)   : Pt := ⟨2*a, 0⟩

/-! ## Weld with the half-shifted row above -/

/-- The plate's TOP vertex coincides with the up-right neighbour's lower-left
shoulder: the rows above are welded at the top vertex. -/
theorem top_meets_upRight_shoulderLL (a b : Int) :
    Pt.add (upRight a b) (shoulderLL a b) = top b := by
  simp only [Pt.add, upRight, shoulderLL, top, Pt.mk.injEq]
  omega

/-- The plate's upper-right shoulder coincides with the up-right neighbour's
bottom vertex: the shared edge (top → shoulderUR) is exactly the neighbour's
(shoulderLL → bottom). No gap, no overlap. -/
theorem shoulderUR_meets_upRight_bottom (a b : Int) :
    Pt.add (upRight a b) (bottom b) = shoulderUR a b := by
  simp only [Pt.add, upRight, bottom, shoulderUR, Pt.mk.injEq]
  omega

/-- Symmetric weld on the left: the TOP vertex also coincides with the up-left
neighbour's lower-right shoulder, so the top vertex is shared by BOTH upper
neighbours (a proper 3-plate junction). -/
theorem top_meets_upLeft_shoulderLR (a b : Int) :
    Pt.add (upLeft a b) (shoulderLR a b) = top b := by
  simp only [Pt.add, upLeft, shoulderLR, top, Pt.mk.injEq]
  omega

/-! ## Weld with the same-row neighbour (shared vertical edge) -/

/-- Same-row neighbour shares the full vertical edge: my upper-right shoulder is
its upper-left shoulder. -/
theorem shoulderUR_meets_sameRow_shoulderUL (a b : Int) :
    Pt.add (sameRow a) (shoulderUL a b) = shoulderUR a b := by
  simp only [Pt.add, sameRow, shoulderUL, shoulderUR, Pt.mk.injEq]
  omega

/-- ...and my lower-right shoulder is its lower-left shoulder. Together with the
above, the entire east edge (shoulderUR → shoulderLR) is shared — no seam. -/
theorem shoulderLR_meets_sameRow_shoulderLL (a b : Int) :
    Pt.add (sameRow a) (shoulderLL a b) = shoulderLR a b := by
  simp only [Pt.add, sameRow, shoulderLL, shoulderLR, Pt.mk.injEq]
  omega

/-! ## Exact area = one grid cell (perfect tiling, no gap/overlap) -/

/-- Twice the signed shoelace area of a closed integer polygon. -/
def shoelace2 : List Pt → Int
  | [] => 0
  | [_] => 0
  | p :: q :: rest => (p.e * q.n - q.e * p.n) + shoelace2 (q :: rest)

/-- Close the ring back to its first vertex, then shoelace. -/
def polyArea2 (pts : List Pt) : Int :=
  match pts with
  | [] => 0
  | p :: _ => shoelace2 (pts ++ [p])

/-- The plate's footprint, via the shoelace formula, equals `12·a·b`, i.e.
twice the cell area `dE·dN = (2a)(3b) = 6ab`. A plate that under/over-covered
its cell (a gap or an overlap) would not hit this exactly. Witnessed at sample
scales (the formula is `12ab`; Init-only so we evaluate rather than `ring`). -/
example : polyArea2 (ring 1 1) = 12 * (1 * 1) := by decide   -- dE=2, dN=3
example : polyArea2 (ring 3 2) = 12 * (3 * 2) := by decide   -- dE=6, dN=6 (square)
example : polyArea2 (ring 2 5) = 12 * (2 * 5) := by decide   -- tall cell
example : polyArea2 (ring 7 1) = 12 * (7 * 1) := by decide   -- wide cell

/-- Restated against the literal cell area `dE·dN = (2a)(3b)`: the shoelace value
is exactly twice it, so each plate tiles its cell with no slack. -/
example : polyArea2 (ring 3 2) = 2 * ((2 * 3) * (3 * 2)) := by decide

/-! ## Why no overlap "fudge"

A concrete witness that scaling the plate (the forbidden overlap factor) breaks
the weld: with `dE = 6` (a = 3), `dN = 6` (b = 2), the exact upper-right shoulder
is `(3, 2)` and meets the up-right neighbour's bottom exactly. A plate whose east
half-width was fudged to `4` puts the shoulder at `(4, 2)`, which no longer meets
the neighbour vertex `(3, 2)` — the "seesaw off horizontally" gap. -/
theorem fudge_breaks_weld_example :
    Pt.add (upRight 3 2) (bottom 2) = shoulderUR 3 2
    ∧ shoulderUR 3 2 ≠ (⟨4, 2⟩ : Pt) := by
  decide

end AnisotropicHexWeld
end Gnosis
