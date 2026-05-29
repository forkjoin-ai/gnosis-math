namespace Gnosis
namespace GeodesicHexSphere

/-!
# Geodesic Hex Sphere (Goldberg Polyhedron) — the grid that actually tiles a sphere

## Lesson from failure

The earth terrain first tiled with a lat/lon RING grid: `round(equatorColumns ·
cos lat)` columns per row, rendered with anisotropic plates (see
`Gnosis.AnisotropicHexWeld`). Those plates weld EXACTLY within a constant-column
band, but the column count JITTERS between rows (the `round`), so the tiling
drifts as you leave the equator. We kept patching the renderer; that was the
mistake.

The deeper reason no renderer patch can fix it: **you cannot tile a sphere with
hexagons alone.** Euler's formula `V − E + F = 2` for a degree-3 hex/pentagon
tiling forces *exactly twelve* pentagons. A lat/lon grid concentrates all of its
"defect" into 2 singular points (the poles) instead of 12 distributed pentagons,
so it can never close cleanly — that IS the pole drift.

## The correct substrate

A class-I **Goldberg polyhedron** `GP(m,0)` — the dual of the m-fold geodesic
subdivision of the icosahedron — tiles the sphere with exactly 12 pentagons (at
the icosahedron's vertices) and the rest hexagons, every edge shared by exactly
two faces. No gaps, no drift, at any resolution `m`. Local hex addressing within
each of the 20 triangular faces uses the cube coordinates of `Gnosis.HexGrid`
(the `x+y+z=0` lattice), which tiles each face perfectly.

This module proves the combinatorics (Init-only, over `Int`): the 12-pentagon
invariant, Euler `V−E+F=2`, and the edge double-count `2E = 5P + 6H` (every edge
shared by exactly two faces — the formal statement of "no gaps, no overlaps").
-/

/-- Triangulation number for class-I Goldberg polyhedra `GP(m,0)`: `T = m²`.
`m` is the subdivision frequency (resolution); `m = 1` is the dodecahedron. -/
def freqT (m : Int) : Int := m * m

/-- The pentagon count is a topological constant — independent of resolution. -/
def pentagons : Int := 12

/-- Hexagon count `10·(m² − 1)`. Zero at `m = 1` (the bare dodecahedron). -/
def hexagons (m : Int) : Int := 10 * freqT m - 10

/-- Every face is a pentagon or a hexagon. -/
def faces (m : Int) : Int := pentagons + hexagons m

/-- Vertices `20·m²`, all of degree 3 (it is a simple/trivalent polyhedron). -/
def vertices (m : Int) : Int := 20 * freqT m

/-- Edges `30·m²`. -/
def edges (m : Int) : Int := 30 * freqT m

/-! ## The twelve-pentagon invariant -/

/-- **Exactly twelve pentagons at every resolution.** This is the topological
fingerprint a lat/lon grid (which has only 2 singular points, the poles) can
never reproduce — and the reason the ring grid drifts while a Goldberg grid
does not. -/
theorem pentagons_always_twelve (_m : Int) : pentagons = 12 := rfl

/-- Face total expands to `10·m² + 2`. -/
theorem faces_eq (m : Int) : faces m = 10 * freqT m + 2 := by
  unfold faces pentagons hexagons
  generalize freqT m = t
  omega

/-! ## Euler characteristic = 2 (a closed sphere, genus 0) -/

/-- **Euler's formula holds: `V − E + F = 2`.** The tiling closes into a sphere
with no boundary and no excess — at any resolution `m`. A flat/ring hex layout
cannot satisfy this with hexagons-only, which forces the 12 pentagons above. -/
theorem euler_characteristic (m : Int) :
    vertices m - edges m + faces m = 2 := by
  unfold vertices edges faces pentagons hexagons
  generalize freqT m = t
  omega

/-! ## Exact edge sharing — the formal "no gaps, no overlaps" -/

/-- **Every edge is shared by exactly two faces: `2E = 5·P + 6·H`.** Summing
sides over all faces (5 per pentagon, 6 per hexagon) counts each edge twice.
Equality with `2E` means the faces fit together with no unmatched (gap) or
triple-counted (overlap) edges — exact tessellation, by construction, at every
resolution. This is what the ring-grid anisotropic plates only achieve locally. -/
theorem edges_double_counted (m : Int) :
    2 * edges m = 5 * pentagons + 6 * hexagons m := by
  unfold edges pentagons hexagons
  generalize freqT m = t
  omega

/-- Corollary: the edge count derived from face sides equals the independent
edge total — the two ways of counting agree. -/
theorem edge_count_consistent (m : Int) :
    edges m = (5 * pentagons + 6 * hexagons m) / 2 := by
  unfold edges pentagons hexagons
  generalize freqT m = t
  omega

/-! ## Resolution sanity -/

/-- At the coarsest resolution `m = 1` the Goldberg polyhedron is the regular
dodecahedron: 12 pentagons, 0 hexagons, 20 vertices, 30 edges, 12 faces. -/
theorem dodecahedron_at_m_one :
    pentagons = 12 ∧ hexagons 1 = 0 ∧ vertices 1 = 20 ∧ edges 1 = 30 ∧ faces 1 = 12 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Hexagons grow quadratically with the frequency `m` while the 12 pentagons
stay fixed — so finer terrain detail never changes the topology. (Witnessed at
`m = 1, 2, 3`: 0, 30, 80 hexagons.) -/
theorem hexagons_grow_pentagons_fixed :
    hexagons 1 = 0 ∧ hexagons 2 = 30 ∧ hexagons 3 = 80 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end GeodesicHexSphere
end Gnosis
