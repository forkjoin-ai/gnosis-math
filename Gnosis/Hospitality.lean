/-
  Hospitality.lean
  ================

  The GENERAL principle behind city placement, home claiming, and spawning: a
  single location-hospitality score `H` for ANY entity, of ANY type. Each entity
  type maps the features that matter to it onto three LEXICOGRAPHIC tiers
  (primary ≫ secondary ≫ tertiary):

      score3 primary secondary tertiary = primary * 1000000 + secondary * 1000 + tertiary

  with each per-feature input bounded in `[0, 999]` (`bounded`) so a lower tier
  can never overtake a higher one — the ordering is strictly lexicographic.

  The point of the abstraction: the SAME score (and the SAME dominance proof)
  serves every type — only the feature→tier mapping differs:

      city        : (riverContact,  orthoRoad,   alongRoad)   -- = Gnosis.CityPlacement
      person/home : (shelter,       safety,      floorView)
      vegetation  : (light,         soil,        space)
      animal      : (food,          shelter,     low-predation)

  So `Gnosis.CityPlacement` (the #32 river>road rule) is exactly the CITY instance
  of hospitality, proven below (`cityPlacement_is_instance`). Claiming = take the
  highest-`H` available site; spawning seeds where `H` is high (the Skyrms
  congestion-equilibrium lives in `Gnosis.HospitalitySpawning`).

  PROVEN (general, `omega` — linear in literal weights, type-agnostic):
    * `primary_dominates`        : more primary-need strictly wins, any bounded lower tiers.
    * `secondary_beats_tertiary` : equal primary, more secondary strictly wins.
    * `monotone_in_primary/secondary/tertiary` : more of a feature never lowers `H`.
  PROVEN (bridge): `cityPlacement_is_instance` : `CityPlacement.score = score3`.
  WITNESSED (`decide`): concrete per-type lexicographic comparisons.

  Init-only Rustic Church. No Mathlib.
-/

import Gnosis.CityPlacement

namespace Gnosis
namespace Hospitality

/-- The general 3-tier lexicographic hospitality score. -/
def score3 (primary secondary tertiary : Int) : Int :=
  primary * 1000000 + secondary * 1000 + tertiary

/-- Standing bound on a per-feature input: in `[0, 999]`, so each tier stays below
    the next weight gap and the ordering is lexicographic. -/
def bounded (n : Int) : Prop := 0 ≤ n ∧ n ≤ 999

/-- The primary need dominates: any advantage in the top tier strictly wins, no
    matter the (bounded) lower tiers. Type-agnostic — this one proof serves every
    entity type's primary need (a city's river, a person's shelter, …). -/
theorem primary_dominates
    (p1 p2 s1 t1 s2 t2 : Int)
    (hp : p1 < p2)
    (hs1 : bounded s1) (ht1 : bounded t1)
    (hs2 : bounded s2) (ht2 : bounded t2) :
    score3 p1 s1 t1 < score3 p2 s2 t2 := by
  unfold score3 bounded at *
  omega

/-- Equal primary need: a stronger secondary tier strictly wins, regardless of the
    (bounded) tertiary terms. -/
theorem secondary_beats_tertiary
    (p s1 t1 s2 t2 : Int)
    (hs : s1 < s2)
    (ht1 : bounded t1) (ht2 : bounded t2) :
    score3 p s1 t1 < score3 p s2 t2 := by
  unfold score3 bounded at *
  omega

/-- More of the primary feature never lowers hospitality. -/
theorem monotone_in_primary (p1 p2 s t : Int) (h : p1 ≤ p2) :
    score3 p1 s t ≤ score3 p2 s t := by
  unfold score3
  omega

/-- More of the secondary feature never lowers hospitality. -/
theorem monotone_in_secondary (p s1 s2 t : Int) (h : s1 ≤ s2) :
    score3 p s1 t ≤ score3 p s2 t := by
  unfold score3
  omega

/-- More of the tertiary feature never lowers hospitality. -/
theorem monotone_in_tertiary (p s t1 t2 : Int) (h : t1 ≤ t2) :
    score3 p s t1 ≤ score3 p s t2 := by
  unfold score3
  omega

/-- The CITY is the city-instance of hospitality: `CityPlacement.score` on
    `(river, ortho, along)` IS `score3`. The #32 river>road placement rule is just
    hospitality specialized to a city's needs. -/
theorem cityPlacement_is_instance (r o a : Int) :
    CityPlacement.score r o a = score3 r o a := by
  unfold CityPlacement.score CityPlacement.wRiver CityPlacement.wOrtho score3
  omega

-- ===========================================================================
-- WITNESSED comparisons (decide): the lexicographic order, per entity type.
-- ===========================================================================

/-- A person prefers SHELTER above all: a sheltered spot (1,0,0) beats an exposed
    one with maximal safety + view (0,999,999). (Same lemma shape serves any type's
    primary need — hospitality is type-agnostic.) -/
theorem primary_need_wins : score3 0 999 999 < score3 1 0 0 := by decide

/-- Equal primary need → the secondary tier breaks the tie (e.g. equal shelter,
    more safety wins over any view). -/
theorem secondary_tiebreak : score3 5 0 999 < score3 5 1 0 := by decide

/-- Full chain: tertiary-only < secondary-only < primary-only. -/
theorem hospitality_chain :
    score3 0 0 5 < score3 0 1 0 ∧ score3 0 999 999 < score3 1 0 0 := by decide

end Hospitality
end Gnosis
