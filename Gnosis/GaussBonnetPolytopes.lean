import Init

/-!
  # Normalized angle-defect Gauss-Bonnet on the Platonic solids.

  This module witnesses the Descartes / angle-defect form of the Gauss-Bonnet
  theorem on the five Platonic solids and, as an optional cross-check, on a
  small square-tiled flat torus. It does not prove the general
  Descartes-Gauss-Bonnet theorem, it does not touch continuous curvature,
  and it makes no Riemannian-geometry claim. Each polytope is realized as a
  record of its combinatorial data, and each theorem is discharged by
  kernel `decide` over `Nat` arithmetic.

  ## Normalization convention

  Under the `Init`-only constraint we have no `π` and no `ℝ`. We normalize
  angles by `2π`, so a full turn around a vertex is `1`. We then choose a
  common denominator large enough to express every face angle of every
  Platonic solid as a whole number:

  * equilateral triangle face angle `π/3` = `1/6` of a full turn,
  * square face angle `π/2` = `1/4` of a full turn,
  * regular pentagon face angle `3π/5` = `3/10` of a full turn.

  The least common denominator of `6`, `4`, and `10` is `60`. Over that
  grid, one full turn = `60`, a triangle angle = `10`, a square angle = `15`,
  a pentagon angle = `18`. The angle defect at a vertex, in sixtieths of a
  full turn, is `60 - facesPerVertex * angleInSixtieths`.

  For a convex polytope, Descartes' theorem says the total angle defect
  equals `4π`, i.e. `2` full turns, i.e. `2 · 60 = 120` sixtieths. This is
  `2πχ` with `χ = 2`, the Euler characteristic of the boundary 2-sphere.

  ## What is proved

  * Per-vertex defects and total defects for tetrahedron, cube, octahedron,
    dodecahedron, icosahedron.
  * For each solid, `totalDefectSixtieths = 2 * 60`, realizing `χ = 2` via
    the normalized Descartes identity.
  * For each solid, `eulerFromDefect = 2`, extracting `χ` by division.
  * For each solid, the combinatorial cross-check `V - E + F = 2` via the
    classical Euler formula.
  * For a `2 × 2` square-tiled flat torus, the combinatorial cross-check
    `V - E + F = 0`. The torus case is combinatorial only, not an
    integrated-curvature statement.

  No `sorry`, no new `axiom`, `import Init` only, kernel `decide` only.
-/

namespace GaussBonnetPolytopes

/-! ### Part 1: Face types and normalized angle encoding.

    Every Platonic solid has a single face type. We encode the three types
    that appear (triangle, square, pentagon) and their face angles as
    integer sixtieths of a full turn.
-/

/-- The face polygons that appear in Platonic solids. -/
inductive FaceType
  | triangle
  | square
  | pentagon
  deriving DecidableEq, Repr

/-- Interior angle of a regular face, measured in sixtieths of a full turn
    (where `60` = `2π`). `π/3 = 10/60`, `π/2 = 15/60`, `3π/5 = 18/60`. -/
def angleInSixtieths : FaceType → Nat
  | FaceType.triangle => 10
  | FaceType.square   => 15
  | FaceType.pentagon => 18

/-! ### Part 2: Combinatorial record for a Platonic solid. -/

/-- Combinatorial data for a regular convex polytope with a single face
    type: the face polygon, how many faces meet at each vertex, and the
    vertex / edge / face counts. -/
structure Polytope where
  name           : String
  faceType       : FaceType
  facesPerVertex : Nat
  vertices       : Nat
  edges          : Nat
  faces          : Nat
  deriving Repr

/-- Angle defect at one vertex, in sixtieths of a full turn. For a convex
    polytope this is `2π - Σ face-angles at v`, normalized by `2π`. -/
def vertexDefectSixtieths (P : Polytope) : Nat :=
  60 - P.facesPerVertex * angleInSixtieths P.faceType

/-- Total angle defect summed over all vertices, in sixtieths of a full
    turn. For convex polytopes Descartes' theorem says this equals
    `2 * 60`, i.e. two full turns, i.e. `2π · χ` with `χ = 2`. -/
def totalDefectSixtieths (P : Polytope) : Nat :=
  P.vertices * vertexDefectSixtieths P

/-- Euler characteristic read off from the normalized total angle defect.
    For a convex polytope this should be `2`. -/
def eulerFromDefect (P : Polytope) : Nat :=
  totalDefectSixtieths P / 60

/-- Combinatorial Euler characteristic `V - E + F`, as an `Int`. -/
def eulerCombinatorial (P : Polytope) : Int :=
  (P.vertices : Int) - (P.edges : Int) + (P.faces : Int)

/-! ### Part 3: The five Platonic solids.

    Vertex / edge / face counts follow the standard tables. `facesPerVertex`
    is the number of faces meeting at each vertex, equal to the vertex
    degree of the face-incidence graph.
-/

/-- Tetrahedron: 4 triangular faces, 3 meeting at each of 4 vertices. -/
def tetrahedron : Polytope :=
  { name := "tetrahedron"
  , faceType := FaceType.triangle
  , facesPerVertex := 3
  , vertices := 4
  , edges := 6
  , faces := 4 }

/-- Cube: 6 square faces, 3 meeting at each of 8 vertices. -/
def cube : Polytope :=
  { name := "cube"
  , faceType := FaceType.square
  , facesPerVertex := 3
  , vertices := 8
  , edges := 12
  , faces := 6 }

/-- Octahedron: 8 triangular faces, 4 meeting at each of 6 vertices. -/
def octahedron : Polytope :=
  { name := "octahedron"
  , faceType := FaceType.triangle
  , facesPerVertex := 4
  , vertices := 6
  , edges := 12
  , faces := 8 }

/-- Dodecahedron: 12 pentagonal faces, 3 meeting at each of 20 vertices. -/
def dodecahedron : Polytope :=
  { name := "dodecahedron"
  , faceType := FaceType.pentagon
  , facesPerVertex := 3
  , vertices := 20
  , edges := 30
  , faces := 12 }

/-- Icosahedron: 20 triangular faces, 5 meeting at each of 12 vertices. -/
def icosahedron : Polytope :=
  { name := "icosahedron"
  , faceType := FaceType.triangle
  , facesPerVertex := 5
  , vertices := 12
  , edges := 30
  , faces := 20 }

/-! ### Part 4: Angle-defect Gauss-Bonnet per solid.

    For each Platonic solid, the total normalized angle defect equals
    `2 * 60` sixtieths of a full turn, i.e. `4π`, realizing `χ = 2`.
-/

/-- Tetrahedron: `Σ defect = 4 · 30 = 120 = 2 · 60`. -/
theorem tetrahedron_total_defect :
    totalDefectSixtieths tetrahedron = 2 * 60 := by
  decide

/-- Cube: `Σ defect = 8 · 15 = 120 = 2 · 60`. -/
theorem cube_total_defect :
    totalDefectSixtieths cube = 2 * 60 := by
  decide

/-- Octahedron: `Σ defect = 6 · 20 = 120 = 2 · 60`. -/
theorem octahedron_total_defect :
    totalDefectSixtieths octahedron = 2 * 60 := by
  decide

/-- Dodecahedron: `Σ defect = 20 · 6 = 120 = 2 · 60`. -/
theorem dodecahedron_total_defect :
    totalDefectSixtieths dodecahedron = 2 * 60 := by
  decide

/-- Icosahedron: `Σ defect = 12 · 10 = 120 = 2 · 60`. -/
theorem icosahedron_total_defect :
    totalDefectSixtieths icosahedron = 2 * 60 := by
  decide

/-! ### Part 5: Euler characteristic extracted from the total defect.

    Dividing the normalized total defect by `60` recovers `χ = 2` for
    each Platonic solid.
-/

theorem tetrahedron_euler_from_defect : eulerFromDefect tetrahedron = 2 := by
  decide

theorem cube_euler_from_defect : eulerFromDefect cube = 2 := by
  decide

theorem octahedron_euler_from_defect : eulerFromDefect octahedron = 2 := by
  decide

theorem dodecahedron_euler_from_defect : eulerFromDefect dodecahedron = 2 := by
  decide

theorem icosahedron_euler_from_defect : eulerFromDefect icosahedron = 2 := by
  decide

/-! ### Part 6: Combinatorial cross-check via `V - E + F = 2`.

    Classical Euler formula for each Platonic solid, verified against the
    same record data.
-/

theorem tetrahedron_euler_combinatorial :
    eulerCombinatorial tetrahedron = 2 := by
  decide

theorem cube_euler_combinatorial :
    eulerCombinatorial cube = 2 := by
  decide

theorem octahedron_euler_combinatorial :
    eulerCombinatorial octahedron = 2 := by
  decide

theorem dodecahedron_euler_combinatorial :
    eulerCombinatorial dodecahedron = 2 := by
  decide

theorem icosahedron_euler_combinatorial :
    eulerCombinatorial icosahedron = 2 := by
  decide

/-! ### Part 7: Flat torus cross-check (combinatorial only).

    A square-tiled `2 × 2` flat torus has `V = 4`, `E = 8`, `F = 4`, so
    `V - E + F = 0`. Every vertex on a flat torus already has full angle
    `2π` around it, so every angle defect is zero and the normalized total
    defect is `0 = 2π · 0 = 2π · χ` with `χ = 0`. We witness only the
    combinatorial identity `V - E + F = 0` here; this is not an integrated
    curvature statement and it does not import a metric.
-/

/-- Combinatorial cell counts of a `2 × 2` square-tiled flat torus. On the
    torus each horizontal row of two squares contributes two horizontal
    edges and two vertices, and likewise vertically, giving 4 vertices,
    8 edges, and 4 square faces. -/
structure ToricSquareTiling where
  vertices : Nat
  edges    : Nat
  faces    : Nat
  deriving Repr

/-- A `2 × 2` square-tiled flat torus. -/
def torus2x2 : ToricSquareTiling :=
  { vertices := 4, edges := 8, faces := 4 }

/-- Combinatorial Euler characteristic of a toric square tiling. -/
def toricEuler (T : ToricSquareTiling) : Int :=
  (T.vertices : Int) - (T.edges : Int) + (T.faces : Int)

/-- The `2 × 2` flat torus tiling has `χ = 0`, combinatorially. -/
theorem torus_euler_zero : toricEuler torus2x2 = 0 := by
  decide

/-- On a flat torus every vertex has full `2π` angle around it, so every
    defect is zero. We encode this by giving a "normalized total defect"
    that is literally `0`, matching `2π · χ` with `χ = 0`. This records
    the numerical match; it is not an integrated curvature proof. -/
def torusNormalizedTotalDefectSixtieths (_T : ToricSquareTiling) : Nat := 0

theorem torus_total_defect_zero :
    torusNormalizedTotalDefectSixtieths torus2x2 = 0 := by
  decide

end GaussBonnetPolytopes
