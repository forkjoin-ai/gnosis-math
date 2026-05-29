namespace Gnosis
namespace OrbitalMechanics

/-!
# Orbital Mechanics — Kepler's laws, structurally

Spec for the monster-studio cosmos layer (sun/moon/planets on real orbits,
`worldsim-celestial.ts propagateCelestialPositions`, aeon-solarium `atlas.ts`).

Init-only (no Mathlib): we cannot prove the continuous eccentric-anomaly / trig
results over the reals here. Instead we prove the **structural/algebraic core**
over integers — the parts that catch real bugs (a propagator that violates
Kepler's 3rd law or angular-momentum conservation is wrong regardless of the
trig):

* **Kepler's 3rd law** as a cross-ratio identity: bodies sharing a system
  constant `q` (`T² = q·a³`) satisfy `T_a²·a_b³ = T_b²·a_a³`.
* **Angular momentum conservation**: a *central* acceleration (parallel to the
  radius vector) exerts zero torque, so `dL/dt = 0`.

Proved with core `Int.mul_comm`/`Int.mul_assoc` + `omega`; real cases witnessed
by `decide`. Continuous orbit propagation is witnessed/tested in TS, not proved
over ℝ here.
-/

/-- **Kepler's 3rd law (cross-ratio form).** If two bodies share the system
constant `q` so that `period² = q · semiMajorAxis³` for each, then
`T_a² · a_b³ = T_b² · a_a³` — the period²/axis³ ratio is the same for both.
`aA`,`aB` are the cubed semi-major axes; `TA`,`TB` the squared periods. -/
theorem kepler_third_cross (q aA aB TA TB : Int)
    (hA : TA = q * aA) (hB : TB = q * aB) :
    TA * aB = TB * aA := by
  subst hA; subst hB
  -- (q*aA)*aB = (q*aB)*aA
  rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm aA aB]

/-- Synthetic exact witnesses of Kepler's 3rd law for arbitrary system constant.
`q = 1`: bodies at a = 2,3,4 (a³ = 8,27,64) have T² = 8,27,64; the cross-ratios
match exactly. -/
example : (8 : Int) * 27 = 27 * 8 := by decide           -- a=2 vs a=3
example : (8 : Int) * 64 = 64 * 8 := by decide           -- a=2 vs a=4
example : (27 : Int) * 64 = 64 * 27 := by decide         -- a=3 vs a=4
-- q = 2: T² = 2·a³ → a=2,3 give T² = 16,54; cross-ratio T_a²·a_b³ = T_b²·a_a³.
example : (16 : Int) * 27 = 54 * 8 := by decide

/-- **Central force ⇒ zero torque.** For an acceleration parallel to the radius
vector (`a = (k·x, k·y)`), the 2D torque `x·a_y − y·a_x` is zero — so angular
momentum `L = x·v_y − y·v_x` is conserved along the orbit. -/
theorem central_force_zero_torque (k x y : Int) :
    x * (k * y) - y * (k * x) = 0 := by
  have hx : x * (k * y) = k * (x * y) := by
    rw [← Int.mul_assoc, Int.mul_comm x k, Int.mul_assoc]
  have hy : y * (k * x) = k * (x * y) := by
    rw [← Int.mul_assoc, Int.mul_comm y k, Int.mul_assoc, Int.mul_comm y x]
  rw [hx, hy]; omega

/-- Witnesses: zero torque under a central force at sample positions/strengths. -/
example : (3 : Int) * (5 * 7) - 7 * (5 * 3) = 0 := by decide
example : (-4 : Int) * (2 * 9) - 9 * (2 * (-4)) = 0 := by decide

/-- **Angular momentum is unchanged by a central-force velocity kick.** If the
velocity gains `(k·x, k·y)` (a radial impulse) over a step, `L = x·v_y − y·v_x`
is preserved: the change is exactly the (zero) torque term. -/
theorem angular_momentum_preserved (x y vx vy k : Int) :
    (x * (vy + k * y) - y * (vx + k * x)) = (x * vy - y * vx) := by
  have hx : x * (k * y) = k * (x * y) := by
    rw [← Int.mul_assoc, Int.mul_comm x k, Int.mul_assoc]
  have hy : y * (k * x) = k * (x * y) := by
    rw [← Int.mul_assoc, Int.mul_comm y k, Int.mul_assoc, Int.mul_comm y x]
  -- x*(vy + k*y) = x*vy + x*(k*y); y*(vx + k*x) = y*vx + y*(k*x)
  rw [Int.mul_add, Int.mul_add, hx, hy]
  omega

end OrbitalMechanics
end Gnosis
