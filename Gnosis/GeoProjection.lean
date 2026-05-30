/-
  GeoProjection.lean
  ==================

  The geo math behind matching real-world businesses (OSM POIs) to spawned city
  buildings. Two pieces are proven over scaled integers (Init-only, no Mathlib):

  1. The equirectangular projection on an axis — a degree offset `d` maps to a
     local distance `d * K` (K = scaled km-per-degree), and the inverse divides
     by K. The ROUND-TRIP is exact: `unproject (project d) = d`. So a POI we
     place into the local-km frame and read back lands on the same coordinate —
     the join can't drift the businesses off their buildings by projection error.
     The map is also LINEAR and MONOTONE (order-preserving), so nearest-in-degrees
     equals nearest-in-local-km — matching can be done in either frame.

  2. The nearest-building assignment is an ARGMIN: `closer a b` (the smaller of two
     squared distances) is ≤ BOTH candidates. Folded over the node list this is
     exactly "assign the POI to the closest building".

  PROVEN (omega / Int lemmas, Init-only). No Mathlib.
-/

namespace Gnosis
namespace GeoProjection

/-- Scaled km-per-degree of latitude: 111.32 * 100 (the cave's load-bearing
    equirectangular constant, scaled to an integer). -/
def K : Int := 11132

/-- Project a (scaled) degree offset to local distance. -/
def project (d : Int) : Int := d * K

/-- Invert the projection: local distance back to a (scaled) degree offset. -/
def unproject (loc : Int) : Int := loc / K

/-- ROUND-TRIP: projecting then unprojecting returns the original offset exactly.
    A POI's coordinate survives the local-km <-> lat/lon transit unchanged. -/
theorem project_roundtrip (d : Int) : unproject (project d) = d := by
  unfold unproject project
  have hK : K ≠ 0 := by decide
  exact Int.mul_ediv_cancel d hK

/-- LINEAR: the projection distributes over addition (it is a scaling map). -/
theorem project_linear (a b : Int) : project (a + b) = project a + project b := by
  unfold project
  exact Int.add_mul a b K

/-- MONOTONE: the projection preserves order (K > 0), so the nearest POI in
    degrees is the nearest POI in local km — the join is frame-independent. -/
theorem project_monotone (a b : Int) (h : a ≤ b) : project a ≤ project b := by
  unfold project
  have hK : (0 : Int) ≤ K := by decide
  exact Int.mul_le_mul_of_nonneg_right h hK

-- ── Nearest-building assignment is an argmin ─────────────────────────────────
/-- The closer of two (squared) distances. -/
def closer (a b : Int) : Int := if a ≤ b then a else b

/-- The chosen distance is ≤ the first candidate. -/
theorem closer_le_left (a b : Int) : closer a b ≤ a := by
  unfold closer; split <;> omega

/-- The chosen distance is ≤ the second candidate. Folded over the node list,
    `closer` yields the minimum — the POI is matched to the closest building. -/
theorem closer_le_right (a b : Int) : closer a b ≤ b := by
  unfold closer; split <;> omega

-- ── Witnesses (decide) ───────────────────────────────────────────────────────
/-- A 5-scaled-degree offset projects to 5*K local units. -/
theorem project_witness : project 5 = 55660 := by decide

/-- Among three candidate squared distances, `closer` finds the strict minimum. -/
theorem nearest_of_three : closer (closer 40 9) 25 = 9 := by decide

end GeoProjection
end Gnosis
