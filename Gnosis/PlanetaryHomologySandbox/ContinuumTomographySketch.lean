/-!
# Discrete Continuum Tomography Sketch

Init-only replacement for the constant-slowness tomography rows.

The historical artifact used real interval integrals.  This module preserves
the computational invariant that a constant slowness over a segment of
integer length has travel time `length * slowness`.
-/

namespace PlanetaryHomologySandbox

/-- A discrete ray segment with Nat length. -/
structure DiscreteSegment where
  length : Nat
deriving Repr, DecidableEq

/-- Constant slowness travel time on one segment. -/
def constantSlownessTravelTime (slowness : Nat) (segment : DiscreteSegment) : Nat :=
  segment.length * slowness

/-- Segment travel time is length times constant slowness. -/
theorem lineIntegral_const_slowness_discrete
    (slowness : Nat)
    (segment : DiscreteSegment) :
    constantSlownessTravelTime slowness segment =
      segment.length * slowness := by
  rfl

/-- A straight ray from `a` to `b` has Nat length `b - a`. -/
def straightRaySegment (a b : Nat) : DiscreteSegment :=
  { length := b - a }

/-- Straight-ray constant slowness travel time. -/
def straightRayTravelTime (slowness a b : Nat) : Nat :=
  constantSlownessTravelTime slowness (straightRaySegment a b)

/-- The straight-ray calculation specializes the constant-segment theorem. -/
theorem straightRayTravelTime_const
    (slowness a b : Nat) :
    straightRayTravelTime slowness a b =
      (b - a) * slowness := by
  rfl

/-- Appending two same-slowness segment lengths is linear. -/
theorem constantSlowness_two_segment_linear
    (slowness len₀ len₁ : Nat) :
    (len₀ + len₁) * slowness =
      len₀ * slowness + len₁ * slowness := by
  exact Nat.add_mul len₀ len₁ slowness

end PlanetaryHomologySandbox
