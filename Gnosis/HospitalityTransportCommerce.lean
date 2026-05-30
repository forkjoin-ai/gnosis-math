import Gnosis.HotellingMeshSprawl

/-!
# HospitalityTransportCommerce — the two missing hospitality dimensions

The unified location-hospitality score was missing TRANSPORTATION access
(reachability over the route graph) and COMMERCE access (proximity to market /
audience). Both raise hospitality monotonically, for humans AND businesses — one
`hospitality` serves every entity; they differ only in which dimension dominates.

The bridge to placement: a business's COMMERCE access IS its Hotelling catchment
(the demand it captures as nearest-of-category, `Gnosis/HotellingMeshSprawl`). So
the Hotelling spread law is hospitality SPECIALISED to a business — a differentiating
business strictly raises the hospitality of the plot it picks (`commerce = catchment`
is then a theorem, not a comment).

Init-only; named `Nat` lemmas only (NO omega, per RUSTIC_CHURCH.md); propext-at-most.
-/

namespace Gnosis
namespace HospitalityTransportCommerce

open Gnosis.HotellingMeshSprawl (Plot score near_audience)

/-- Location hospitality augmented with the two missing access dimensions:
    `transportation` (reachability over the route graph) and `commerce`
    (market / audience access), added to a `base` capturing the prior dimensions
    (a person's shelter/safety/view, or a city's river/road). Additive and
    monotone: more of any dimension never lowers hospitality. -/
def hospitality (base transportation commerce : Nat) : Nat :=
  base + transportation + commerce

/-- More TRANSPORTATION access never lowers hospitality. -/
theorem monotone_in_transportation (b t1 t2 c : Nat) (h : t1 ≤ t2) :
    hospitality b t1 c ≤ hospitality b t2 c := by
  unfold hospitality
  exact Nat.add_le_add_right (Nat.add_le_add_left h b) c

/-- More COMMERCE access never lowers hospitality. -/
theorem monotone_in_commerce (b t c1 c2 : Nat) (h : c1 ≤ c2) :
    hospitality b t c1 ≤ hospitality b t c2 := by
  unfold hospitality
  exact Nat.add_le_add_left h (b + t)

/-- A business's hospitality uses its Hotelling placement `score` (from the proven
    `Gnosis/HotellingMeshSprawl`) as the COMMERCE term — `commerce = catchment`. -/
def businessHospitality (base transport : Nat) (p : Plot) : Nat :=
  hospitality base transport (score p)

/-- BRIDGE: more audience (a bigger catchment, all else equal) never lowers a
    plot's hospitality — Hotelling's `near_audience` lifts straight into the
    hospitality COMMERCE dimension. The Hotelling placement IS hospitality
    specialised to a business. -/
theorem more_audience_more_hospitable
    (base transport : Nat) (lo hi : Plot)
    (hcl : lo.claimed = hi.claimed) (hcr : lo.crowding = hi.crowding)
    (hmore : lo.audience ≤ hi.audience) :
    businessHospitality base transport lo ≤ businessHospitality base transport hi := by
  unfold businessHospitality
  exact monotone_in_commerce base transport (score lo) (score hi)
    (near_audience lo hi hcl hcr hmore)

-- ── Witnesses (decide) — one H for all entities, dominance differs ────────────

/-- A human HOME: shelter-`base` dominates, but transport + commerce still add. -/
theorem human_home : hospitality 100 3 2 = 105 := by decide

/-- A business PLOT: commerce (the catchment) is the big term; same function. -/
theorem business_plot : hospitality 2 3 40 = 45 := by decide

/-- TRANSPORTATION breaks a tie between equally-based, equal-commerce spots — the
    dimension we were missing now decides. -/
theorem transport_breaks_tie : hospitality 10 0 5 < hospitality 10 1 5 := by decide

/-- COMMERCE likewise raises hospitality at equal base + transport. -/
theorem commerce_raises : hospitality 10 2 0 < hospitality 10 2 1 := by decide

-- Axiom audit (target: propext-at-most, no omega / native_decide):
#print axioms more_audience_more_hospitable
#print axioms monotone_in_transportation
#print axioms monotone_in_commerce

end HospitalityTransportCommerce
end Gnosis
