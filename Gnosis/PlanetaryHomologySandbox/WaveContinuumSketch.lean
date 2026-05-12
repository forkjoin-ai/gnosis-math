/-!
# Discrete Advection Sketch

Init-only transport witness for the planetary wave-advection row.

The historical artifact proved the differentiable real theorem for
`u(t,x)=f(x−ct)`.  This replacement records the discrete invariant behind
that PDE: after one time step, a profile translated by velocity `c` reads the
same upstream index.
-/

namespace PlanetaryHomologySandbox

/-- A Nat-safe upstream coordinate for a right-moving transport profile. -/
def upstreamIndex (c t x : Nat) : Nat :=
  x - c * t

/-- Discrete transported profile `u(t,x)=f(x−ct)` over Nat indices. -/
def transportedProfile (f : Nat → Nat) (c t x : Nat) : Nat :=
  f (upstreamIndex c t x)

/--
Moving time forward by one and space forward by exactly `c` preserves the
upstream coordinate, provided the current position already dominates `c*t`.
-/
theorem upstreamIndex_transport_step
    (c t x : Nat)
    (_hReachable : c * t ≤ x) :
    upstreamIndex c (t + 1) (x + c) = upstreamIndex c t x := by
  unfold upstreamIndex
  rw [Nat.mul_add, Nat.mul_one]
  exact Nat.add_sub_add_right x c (c * t)

/-- The discrete transported profile is invariant along its transport ray. -/
theorem transportedProfile_transport_step
    (f : Nat → Nat)
    (c t x : Nat)
    (hReachable : c * t ≤ x) :
    transportedProfile f c (t + 1) (x + c) =
      transportedProfile f c t x := by
  unfold transportedProfile
  rw [upstreamIndex_transport_step c t x hReachable]

/-- Unit-speed specialization: `u(t+1,x+1)=u(t,x)` along reachable rays. -/
theorem transportedProfile_unit_speed_step
    (f : Nat → Nat)
    (t x : Nat)
    (hReachable : t ≤ x) :
    transportedProfile f 1 (t + 1) (x + 1) =
      transportedProfile f 1 t x := by
  exact transportedProfile_transport_step f 1 t x (by simpa using hReachable)

end PlanetaryHomologySandbox
