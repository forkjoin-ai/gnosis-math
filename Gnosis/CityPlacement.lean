/-
  CityPlacement.lean
  ==================

  Backs the city-spawn rule in monster-studio's Earth: when choosing where a
  city seeds, the site-selector PREFERS, in strict order,

    (1) adjacency to RIVERS  — maximize water contact;
    (2) else ORTHOGONAL / across a major ROAD (a crossing);
    (3) else ALONG a ROAD.

  We formalize the preference order as a single integer `score` with large
  weight gaps so the three features are LEXICOGRAPHIC: any river advantage
  dominates any orthogonal-road advantage, which dominates any along-road
  advantage, provided the lower-tier inputs are bounded below the next weight.

      score r o a = r * 1000000 + o * 1000 + a

  with the standing bound that each per-feature input lies in `[0, 999]`
  (`bounded`), so the `o`-term can never reach the river weight and the `a`-term
  can never reach the ortho weight. Under that bound the ranking is strict and
  well-ordered.

  PROVEN (general, by `omega` — everything is linear in literal weights):
    * `river_dominates`    : strictly more river contact ⇒ strictly higher score,
                             regardless of the (bounded) road terms.
    * `ortho_beats_along`  : equal river contact, strictly more orthogonal-road
                             crossing ⇒ strictly higher score, regardless of the
                             (bounded) along-road terms.
    * `monotone_in_river`  : `r1 ≤ r2 → score r1 o a ≤ score r2 o a`
                             (more water contact never lowers the score).

  WITNESSED (specific, by `decide`):
    * a river-site beats a road-crossing site beats an along-road site.

  Init-only Rustic Church. No Mathlib.
-/

namespace Gnosis
namespace CityPlacement

/-- River weight: dominates everything below. -/
def wRiver : Int := 1000000

/-- Orthogonal-road (crossing) weight: dominates the along-road term. -/
def wOrtho : Int := 1000

/-- The lexicographic site score. `riverContact`, `orthoRoad`, `alongRoad` are
    nonnegative feature counts; weight gaps make the ordering lexicographic. -/
def score (riverContact orthoRoad alongRoad : Int) : Int :=
  riverContact * wRiver + orthoRoad * wOrtho + alongRoad

/-- Standing bound on a per-feature input: in `[0, 999]`. With this bound the
    `orthoRoad` term stays under `wRiver` and the `alongRoad` term under `wOrtho`,
    which is exactly what makes the lexicographic gaps hold. -/
def bounded (n : Int) : Prop := 0 ≤ n ∧ n ≤ 999

/-- More river contact strictly wins, no matter the (bounded) road terms.
    A site touching the river always beats one that touches it less. -/
theorem river_dominates
    (r1 r2 o1 a1 o2 a2 : Int)
    (hr : r1 < r2)
    (ho1 : bounded o1) (ha1 : bounded a1)
    (ho2 : bounded o2) (ha2 : bounded a2) :
    score r1 o1 a1 < score r2 o2 a2 := by
  unfold score wRiver wOrtho bounded at *
  omega

/-- With equal river contact, a stronger orthogonal-road crossing strictly wins,
    no matter the (bounded) along-road terms. -/
theorem ortho_beats_along
    (r o1 a1 o2 a2 : Int)
    (ho : o1 < o2)
    (ha1 : bounded a1) (ha2 : bounded a2) :
    score r o1 a1 < score r o2 a2 := by
  unfold score wRiver wOrtho bounded at *
  omega

/-- More water contact never lowers the score (monotone in the river term). -/
theorem monotone_in_river
    (r1 r2 o a : Int)
    (h : r1 ≤ r2) :
    score r1 o a ≤ score r2 o a := by
  unfold score wRiver wOrtho
  omega

-- ===========================================================================
-- WITNESSED comparisons (decide): river-site > road-crossing-site > along-site.
-- ===========================================================================

/-- A river-adjacent site (1 river contact, no roads) beats a pure road-crossing
    site (0 river, 999 ortho, 999 along) — even at maximal road advantage. -/
theorem river_site_beats_crossing :
    score 0 999 999 < score 1 0 0 := by decide

/-- A road-crossing site beats an along-road-only site (equal/zero river). -/
theorem crossing_beats_along :
    score 0 0 999 < score 0 1 0 := by decide

/-- Full chain: along-site < crossing-site < river-site. -/
theorem placement_chain :
    score 0 0 5 < score 0 1 0 ∧ score 0 999 999 < score 1 0 0 := by decide

end CityPlacement
end Gnosis
