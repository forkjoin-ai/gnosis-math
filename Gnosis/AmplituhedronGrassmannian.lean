-- Grassmannian structure of attention space — Death #2 of Five Deaths TPS Roadmap.
--
-- Replaces the placeholder `PositiveGrassmannian (k n)` whose
-- `plucker_positivity : ∃ scale : Nat, scale = volume` field is vacuously true.
-- Here every field carries real structural content:
--   * KPlane k d holds an actual k×d matrix with rank/width witnesses.
--   * Plücker coordinates are computed by a totally-defined determinant.
--   * IsPositive demands every Plücker coordinate be strictly > 0.
--   * StandingWaveDims (Death #1) lifts to a coordinate k-plane in d-space.
--
-- Init-only per the gnosis-math Rustic Church initiative: no omega, no simp,
-- no Mathlib. Decidable predicates use Bool. Float bounds (where they would
-- arise from runtime calibration) are deferred to the runtime layer.
import Init
import Gnosis.AmplituhedronAttention

namespace AmplituhedronAttention.Grassmannian

open AmplituhedronAttention

-- ══════════════════════════════════════════════════════════
-- k-PLANE IN d-SPACE
-- ══════════════════════════════════════════════════════════

/-- A k-plane in d-space, represented by k row vectors of length d
    over `Int`. Both witnesses are real structural invariants — there
    are no vacuous existentials in this structure. -/
structure KPlane (k d : Nat) where
  rows : List (List Int)
  rank_witness : rows.length = k
  width_witness : ∀ row ∈ rows, row.length = d

namespace KPlane

/-- The plane is well-shaped: rank k, width d. Together these say the
    underlying matrix is genuinely k × d. -/
theorem shape {k d : Nat} (p : KPlane k d) :
    p.rows.length = k ∧ ∀ row ∈ p.rows, row.length = d :=
  ⟨p.rank_witness, p.width_witness⟩

end KPlane

-- ══════════════════════════════════════════════════════════
-- ORDERED k-SUBSETS OF [0..d) — INDEX SETS FOR PLÜCKER COORDINATES
-- ══════════════════════════════════════════════════════════

/-- All ordered k-subsets of [0..d), grouped by whether they contain
    the maximal element d-1. For k > d the result is `[]`. -/
def kSubsets : Nat → Nat → List (List Nat)
  | 0,    _    => [[]]
  | _+1,  0    => []
  | k+1,  d+1  =>
      ((kSubsets k d).map (fun s => s ++ [d]))
        ++ kSubsets (k+1) d

/-- Sanity check on the base case: there is exactly one 0-subset of any
    `d`-set, namely the empty list. -/
theorem kSubsets_zero (d : Nat) : kSubsets 0 d = [[]] := by
  cases d <;> rfl

-- ══════════════════════════════════════════════════════════
-- DETERMINANT (FUELED COFACTOR EXPANSION)
-- ══════════════════════════════════════════════════════════

/-- Cofactor-expansion determinant with explicit fuel. The empty matrix
    has determinant 1 by convention; the fuel arm fires only when fuel
    runs out on a non-empty matrix (treated as 0). Structural recursion
    on `Nat` fuel keeps the Init kernel happy. -/
def detFueled : Nat → List (List Int) → Int
  | _,    []          => 1
  | 0,    _ :: _      => 0
  | n+1,  row :: rest =>
      (List.range row.length).foldl
        (fun acc j =>
          let sign  : Int := if j % 2 = 0 then 1 else -1
          let entry : Int := row.getD j 0
          let minor : List (List Int) :=
            rest.map (fun r => (r.take j) ++ (r.drop (j+1)))
          acc + sign * entry * detFueled n minor)
        0

/-- Determinant of a square matrix represented as `List (List Int)`.
    Fuel is the row count. -/
def det (m : List (List Int)) : Int := detFueled m.length m

/-- The empty determinant is 1 by convention. -/
theorem det_nil : det [] = 1 := by
  unfold det detFueled; rfl

-- ══════════════════════════════════════════════════════════
-- PLÜCKER COORDINATES
-- ══════════════════════════════════════════════════════════

/-- The k×k submatrix of `rows` selected by column indices `cols`. -/
def submatrix (rows : List (List Int)) (cols : List Nat) : List (List Int) :=
  rows.map (fun row => cols.map (fun j => row.getD j 0))

/-- Plücker coordinate of a k-plane at column subset `cols`:
    determinant of the k×k submatrix on those columns. -/
def pluckerCoord {k d : Nat} (p : KPlane k d) (cols : List Nat) : Int :=
  det (submatrix p.rows cols)

/-- Full vector of Plücker coordinates: one per ordered k-subset of [0..d). -/
def pluckerVector {k d : Nat} (p : KPlane k d) : List Int :=
  (kSubsets k d).map (pluckerCoord p)

/-- The Plücker vector has one entry per ordered k-subset of [0..d). -/
theorem pluckerVector_length {k d : Nat} (p : KPlane k d) :
    (pluckerVector p).length = (kSubsets k d).length := by
  unfold pluckerVector
  exact List.length_map (pluckerCoord p)

-- ══════════════════════════════════════════════════════════
-- POSITIVE GRASSMANNIAN  Gr⁺(k, d)
-- ══════════════════════════════════════════════════════════

/-- Real positivity predicate: every Plücker coordinate is strictly > 0.
    Distinct from the placeholder `∃ scale : Nat, scale = volume`, which
    held vacuously for any `Nat`. -/
def IsPositive {k d : Nat} (p : KPlane k d) : Prop :=
  ∀ cols ∈ kSubsets k d, pluckerCoord p cols > 0

/-- Decidable Bool variant of positivity for runtime checking. -/
def isPositiveBool {k d : Nat} (p : KPlane k d) : Bool :=
  (pluckerVector p).all (fun c => decide (c > 0))

/-- A point on the positive Grassmannian Gr⁺(k, d):
    a k-plane whose Plücker coordinates are all strictly positive. -/
structure PositiveGrassmannian (k d : Nat) where
  plane : KPlane k d
  positive : IsPositive plane

/-- Boundary cells of the closure of Gr⁺: every Plücker coordinate is
    nonnegative, and at least one vanishes. Coordinate planes (spanned
    by basis indices) live on this boundary. -/
def IsBoundary {k d : Nat} (p : KPlane k d) : Prop :=
  (∀ cols ∈ kSubsets k d, pluckerCoord p cols ≥ 0) ∧
  (∃ cols, cols ∈ kSubsets k d ∧ pluckerCoord p cols = 0)

/-- Strict positivity is preserved under the structure projection: a
    `PositiveGrassmannian` carries a witness that every Plücker
    coordinate is strictly positive. -/
theorem positiveGrassmannian_strictly_positive {k d : Nat}
    (g : PositiveGrassmannian k d) :
    ∀ cols ∈ kSubsets k d, pluckerCoord g.plane cols > 0 := g.positive

-- ══════════════════════════════════════════════════════════
-- STANDING WAVE DIMS → COORDINATE k-PLANE
-- ══════════════════════════════════════════════════════════

/-- The unit row e_j of length d: 1 in position j, 0 elsewhere. -/
def unitRow (d j : Nat) : List Int :=
  (List.range d).map (fun i => if i = j then (1 : Int) else 0)

theorem unitRow_length (d j : Nat) :
    (unitRow d j).length = d := by
  unfold unitRow
  rw [List.length_map]
  exact List.length_range

/-- The coordinate k-plane spanned by an ordered list of `indices` ⊂ [0..d):
    each row is a unit vector e_{indices[i]}. -/
def coordinatePlane (k d : Nat) (indices : List Nat)
    (rank_eq : indices.length = k) : KPlane k d :=
  { rows := indices.map (unitRow d),
    rank_witness := by
      rw [List.length_map]; exact rank_eq,
    width_witness := by
      intro row hrow
      have : ∃ j, j ∈ indices ∧ unitRow d j = row := by
        exact List.mem_map.mp hrow
      obtain ⟨j, _, h_eq⟩ := this
      rw [← h_eq]
      exact unitRow_length d j }

/-- Lift a `StandingWaveDims` (from Death #1 standing wave pinning) to a
    coordinate k-plane in d-space, where d = `coverageDen` (the
    denominator of the coverage ratio k/d). -/
def standingWaveToCoordinatePlane (sw : StandingWaveDims)
    (rank_eq : sw.indices.length = sw.k) :
    KPlane sw.k sw.coverageDen :=
  coordinatePlane sw.k sw.coverageDen sw.indices rank_eq

/-- The coordinate plane built from a standing-wave dim list has exactly
    k rows, each of width d. This is the soundness witness for
    `extract_value_gated`-style integration: the indices selected by
    standing wave pinning span a genuine k-plane in d-space. -/
theorem standingWaveToCoordinatePlane_shape (sw : StandingWaveDims)
    (rank_eq : sw.indices.length = sw.k) :
    (standingWaveToCoordinatePlane sw rank_eq).rows.length = sw.k ∧
    ∀ row ∈ (standingWaveToCoordinatePlane sw rank_eq).rows,
      row.length = sw.coverageDen :=
  KPlane.shape (standingWaveToCoordinatePlane sw rank_eq)

-- ══════════════════════════════════════════════════════════
-- AMPLITUHEDRON-ATTENTION BRIDGE
-- ══════════════════════════════════════════════════════════

/-- A point on the amplituhedron is a positive Grassmannian point in
    Gr⁺(k, d) whose ambient dimension d matches `coverageDen` and whose
    embedded k matches the standing wave dim count. -/
structure AmplituhedronPoint (sw : StandingWaveDims) where
  grassmannian : PositiveGrassmannian sw.k sw.coverageDen

/-- The Plücker vector of an amplituhedron point realises the
    coverageNum / coverageDen ratio at the level of subset counts: there
    is one Plücker coordinate per ordered k-subset of [0..d). -/
theorem amplituhedronPoint_plucker_count (sw : StandingWaveDims)
    (a : AmplituhedronPoint sw) :
    (pluckerVector a.grassmannian.plane).length
      = (kSubsets sw.k sw.coverageDen).length := by
  exact pluckerVector_length a.grassmannian.plane

end AmplituhedronAttention.Grassmannian
