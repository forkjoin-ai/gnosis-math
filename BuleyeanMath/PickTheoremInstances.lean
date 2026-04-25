import Init

/-!
# Pick's Theorem on Small Lattice Polygon Instances

Pick's theorem states that for a simple lattice polygon with `B`
boundary lattice points and `I` interior lattice points, the area is

    A = I + B/2 - 1.

To stay inside `Int` and avoid halves, we clear the fraction and
witness the equivalent identity

    2 · A = 2 · I + B - 2.

This module witnesses the identity on a hand-picked list of small
polygons. For each polygon we:

- encode the vertices as a `List (Int × Int)`,
- compute `2 · A` by the shoelace formula (kept in `Int` to remain
  exact and to avoid committing to a sign convention for the area
  itself; we take the absolute value at the end),
- compute the boundary count `B` as the sum of `gcd(|Δx|, |Δy|)`
  over directed edges (a standard reformulation of the
  lattice-points-on-a-segment count that automatically avoids
  double-counting shared vertices on a closed polygon),
- give the interior count `I` as a hand-computed literal, and
- close `2 · (shoelace A) = 2 · I + B - 2` by kernel `decide`.

The general theorem (over all simple lattice polygons, proved by
triangulation and an additivity argument) is not proved here. What
we provide is a finite list of computed coincidences that the
general theorem implies. In particular:

- Interior counts are literals, not computed by a general algorithm.
- The "simple polygon" hypothesis is not checked formally here; the
  input lists are simple by construction.
- `shoelaceTwiceArea` returns `2 · A` as a non-negative `Int`, so
  halves never appear.

All proofs close by kernel `decide`. No `sorry`, no new `axiom`,
`Init`-only.
-/

namespace BuleyeanMath
namespace PickTheoremInstances

/-! ## Integer absolute value and a fueled `Nat` gcd -/

/-- Absolute value of an integer, as a `Nat`. -/
def intAbs (a : Int) : Nat :=
  match a with
  | Int.ofNat n => n
  | Int.negSucc n => Nat.succ n

/-- Euclidean `gcd` on `Nat` with an explicit fuel parameter to keep
termination and kernel reduction straightforward. The fuel is taken
as `a + b + 1` at the call site, which is always an upper bound on
the number of Euclidean steps required. -/
def gcdFuel : Nat → Nat → Nat → Nat
  | 0,           a, _ => a
  | Nat.succ _,  a, 0 => a
  | Nat.succ f,  a, Nat.succ b => gcdFuel f (Nat.succ b) (a % Nat.succ b)

/-- Euclidean `gcd` on `Nat`. -/
def gcdNat (a b : Nat) : Nat := gcdFuel (a + b + 1) a b

/-! ## Sanity checks on `gcdNat` -/

theorem gcdNat_2_0  : gcdNat 2 0 = 2 := by decide
theorem gcdNat_0_3  : gcdNat 0 3 = 3 := by decide
theorem gcdNat_4_6  : gcdNat 4 6 = 2 := by decide
theorem gcdNat_9_12 : gcdNat 9 12 = 3 := by decide
theorem gcdNat_3_3  : gcdNat 3 3 = 3 := by decide

/-! ## Shoelace formula, returning `2 · A`

For a polygon with vertices `v_0, v_1, …, v_{n-1}` taken in order
(with the closing edge `v_{n-1} → v_0` implicit), the signed area is

    A = (1 / 2) · Σ_i (x_i · y_{i+1} - x_{i+1} · y_i).

We sum the integer term, take the absolute value, and return the
resulting non-negative `Int`. This is exactly `2 · A`.
-/

/-- Walk the vertex list with the previous vertex threaded through,
accumulating the signed shoelace sum. Returns the raw (possibly
negative) `Int`. -/
def shoelaceSumAux (first : Int × Int)
    : (Int × Int) → List (Int × Int) → Int
  | prev, [] =>
      prev.fst * first.snd - first.fst * prev.snd
  | prev, next :: rest =>
      (prev.fst * next.snd - next.fst * prev.snd)
        + shoelaceSumAux first next rest

/-- Signed shoelace sum over a vertex list, with the closing edge
from the last vertex back to the first handled implicitly. -/
def shoelaceSum : List (Int × Int) → Int
  | [] => 0
  | [_] => 0
  | v0 :: v1 :: rest =>
      (v0.fst * v1.snd - v1.fst * v0.snd) + shoelaceSumAux v0 v1 rest

/-- Non-negative `Int`, equal to `2 · A` for a simple polygon. -/
def shoelaceTwiceArea (verts : List (Int × Int)) : Int :=
  Int.ofNat (intAbs (shoelaceSum verts))

/-! ## Boundary lattice-point count

For a directed segment from `p` to `q`, the number of lattice
points strictly between `p` and `q` plus one endpoint is
`gcd(|Δx|, |Δy|)`. Summed over all directed edges of a closed
polygon this double-counts no vertex and returns exactly the
total boundary lattice-point count `B`.
-/

/-- `gcd(|Δx|, |Δy|)` for a single directed edge `p → q`. -/
def edgeGcd (p q : Int × Int) : Nat :=
  gcdNat (intAbs (q.fst - p.fst)) (intAbs (q.snd - p.snd))

/-- Sum edge-gcds along the list, with the closing edge from `last`
back to `first` handled at the `[]` base. -/
def boundarySumAux (first : Int × Int)
    : (Int × Int) → List (Int × Int) → Nat
  | prev, [] => edgeGcd prev first
  | prev, next :: rest =>
      edgeGcd prev next + boundarySumAux first next rest

/-- Boundary lattice-point count `B` for a closed lattice polygon. -/
def boundaryCount : List (Int × Int) → Nat
  | [] => 0
  | [_] => 0
  | v0 :: v1 :: rest => edgeGcd v0 v1 + boundarySumAux v0 v1 rest

/-! ## Pick identity, `Int` form

We write Pick as `2 · A = 2 · I + B - 2` with both sides in `Int`,
so that the subtraction of `2` is well-defined. For every polygon
we witness `shoelaceTwiceArea = 2 · I + B - 2` with `B ≥ 2`.
-/

/-- Right-hand side `2 · I + B - 2` as an `Int`. -/
def pickRHS (interior : Nat) (boundary : Nat) : Int :=
  (Int.ofNat (2 * interior + boundary)) - 2

/-! ## Polygon 1: unit square `[0,0] - [1,0] - [1,1] - [0,1]`

`A = 1`, `B = 4`, `I = 0`. Check: `2 · 1 = 2 · 0 + 4 - 2 = 2`.
-/

def unitSquare : List (Int × Int) :=
  [(0, 0), (1, 0), (1, 1), (0, 1)]

def I_unitSquare : Nat := 0

theorem shoelace_unit_square :
    shoelaceTwiceArea unitSquare = 2 := by decide

theorem boundary_unit_square :
    boundaryCount unitSquare = 4 := by decide

theorem pick_unit_square :
    shoelaceTwiceArea unitSquare
      = pickRHS I_unitSquare (boundaryCount unitSquare) := by decide

/-! ## Polygon 2: triangle `[0,0] - [2,0] - [0,2]`

`A = 2`, `B = 6`, `I = 0`. Check: `4 = 0 + 6 - 2`.
-/

def triangle2 : List (Int × Int) :=
  [(0, 0), (2, 0), (0, 2)]

def I_triangle2 : Nat := 0

theorem shoelace_triangle_2 :
    shoelaceTwiceArea triangle2 = 4 := by decide

theorem boundary_triangle_2 :
    boundaryCount triangle2 = 6 := by decide

theorem pick_triangle_2 :
    shoelaceTwiceArea triangle2
      = pickRHS I_triangle2 (boundaryCount triangle2) := by decide

/-! ## Polygon 3: triangle `[0,0] - [3,0] - [0,3]`

`A = 9/2`, so `2A = 9`. `B = 9`, `I = 1`. Check: `9 = 2 + 9 - 2`.
-/

def triangle3 : List (Int × Int) :=
  [(0, 0), (3, 0), (0, 3)]

def I_triangle3 : Nat := 1

theorem shoelace_triangle_3 :
    shoelaceTwiceArea triangle3 = 9 := by decide

theorem boundary_triangle_3 :
    boundaryCount triangle3 = 9 := by decide

theorem pick_triangle_3 :
    shoelaceTwiceArea triangle3
      = pickRHS I_triangle3 (boundaryCount triangle3) := by decide

/-! ## Polygon 4: rectangle `[0,0] - [3,0] - [3,2] - [0,2]`

`A = 6`, `B = 10`, `I = 2`. Check: `12 = 4 + 10 - 2`.
-/

def rectangle3x2 : List (Int × Int) :=
  [(0, 0), (3, 0), (3, 2), (0, 2)]

def I_rectangle3x2 : Nat := 2

theorem shoelace_rectangle_3_2 :
    shoelaceTwiceArea rectangle3x2 = 12 := by decide

theorem boundary_rectangle_3_2 :
    boundaryCount rectangle3x2 = 10 := by decide

theorem pick_rectangle_3_2 :
    shoelaceTwiceArea rectangle3x2
      = pickRHS I_rectangle3x2 (boundaryCount rectangle3x2) := by decide

/-! ## Polygon 5: L-shape hexagon

Vertices `[0,0] - [2,0] - [2,1] - [1,1] - [1,2] - [0,2]`.
`A = 3`, `B = 8`, `I = 0`. Check: `6 = 0 + 8 - 2`.
-/

def lHex : List (Int × Int) :=
  [(0, 0), (2, 0), (2, 1), (1, 1), (1, 2), (0, 2)]

def I_lHex : Nat := 0

theorem shoelace_L_hex :
    shoelaceTwiceArea lHex = 6 := by decide

theorem boundary_L_hex :
    boundaryCount lHex = 8 := by decide

theorem pick_L_hex :
    shoelaceTwiceArea lHex
      = pickRHS I_lHex (boundaryCount lHex) := by decide

/-! ## Polygon 6: non-axis-aligned triangle `[0,0] - [4,1] - [1,4]`

`A = 15/2`, so `2A = 15`. Edge-gcds: `gcd(4,1) = 1`, `gcd(3,3) = 3`,
`gcd(1,4) = 1`, giving `B = 5`. Pick then forces `I = 6`. Check:
`15 = 12 + 5 - 2 = 15`.
-/

def triangle414 : List (Int × Int) :=
  [(0, 0), (4, 1), (1, 4)]

def I_triangle414 : Nat := 6

theorem shoelace_triangle_4_1_1_4 :
    shoelaceTwiceArea triangle414 = 15 := by decide

theorem boundary_triangle_4_1_1_4 :
    boundaryCount triangle414 = 5 := by decide

theorem pick_triangle_4_1_1_4 :
    shoelaceTwiceArea triangle414
      = pickRHS I_triangle414 (boundaryCount triangle414) := by decide

end PickTheoremInstances
end BuleyeanMath
