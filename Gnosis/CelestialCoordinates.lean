/-
  CelestialCoordinates.lean
  =========================

  Backs the real starfield in monster-studio's Earth (Phase 3): stars are placed
  on the celestial sphere from catalog RA/Dec, then drawn as a unit direction
  scaled out to a fixed render radius. This module formalizes the STRUCTURAL
  guarantees of that placement over scaled-integer coordinates.

  A direction is carried as integers (x, y, z). On the render sphere we use a
  scaled radius `R = 1000`, so a point sitting exactly on the celestial sphere
  satisfies `normSq x y z = x*x + y*y + z*z = R*R = 1000000`.

  PROVEN (general, open-variable, by Int arithmetic / ring):
    * `scale_normSq`     : scaling a direction by `k` multiplies `normSq` by `k*k`
                           (so a unit direction scaled by `R` lands at `R*R · unitNormSq`).
    * `antipode_normSq`  : the opposite point `(-x,-y,-z)` has the same `normSq`
                           (the antipode sits on the same sphere).

  WITNESSED (specific, by `decide` on concrete integer coordinates):
    * `round_trip` lemmas: a handful of integer (x,y,z) chosen on the R=1000
      sphere `decide` that `normSq = 1000000`.

  HONESTY NOTE: the trig map RA/Dec -> (x,y,z) is NOT computable in Init (no
  sin/cos over the reals). We therefore PROVE the norm/antipode identities over
  the resulting integer coordinates and WITNESS specific stars by `decide` on
  pre-rounded integer triples. We do not claim to derive the triples from the
  catalog here.

  Init-only Rustic Church. No Mathlib.
-/

namespace Gnosis
namespace CelestialCoordinates

/-- Scaled render radius of the celestial sphere. -/
def R : Int := 1000

/-- Squared Euclidean norm of an integer direction/point. -/
def normSq (x y z : Int) : Int := x * x + y * y + z * z

/-- The target squared radius on the render sphere: `R*R = 1000000`. -/
def radiusSq : Int := R * R

/-- Scaling a direction by `k` multiplies its squared norm by `k*k`.
    Specialized to `k = R`, this is exactly "scale a unit vector by `R`":
    `normSq (R*x) (R*y) (R*z) = (R*R) * normSq x y z`. -/
theorem scale_normSq (k x y z : Int) :
    normSq (k * x) (k * y) (k * z) = (k * k) * normSq x y z := by
  unfold normSq
  rw [Int.mul_add, Int.mul_add]
  congr 1
  · congr 1
    · ac_rfl
    · ac_rfl
  · ac_rfl

/-- A unit direction (squared norm `1`) scaled by `R` lands with squared norm
    `R*R = radiusSq` — it sits exactly on the celestial sphere. -/
theorem unit_scaled_on_sphere (x y z : Int) (hu : normSq x y z = 1) :
    normSq (R * x) (R * y) (R * z) = radiusSq := by
  rw [scale_normSq, hu]
  unfold radiusSq
  rw [Int.mul_one]

/-- The antipode `(-x,-y,-z)` has the same squared norm — it sits on the same
    sphere. Proven generally: `(-x)*(-x) = x*x`, etc. -/
theorem antipode_normSq (x y z : Int) :
    normSq (-x) (-y) (-z) = normSq x y z := by
  unfold normSq
  rw [Int.neg_mul_neg, Int.neg_mul_neg, Int.neg_mul_neg]

/-- The squared norm only depends on each coordinate through its square, so the
    sign of each axis is irrelevant (a stronger, per-axis form of antipode). -/
theorem normSq_neg_x (x y z : Int) :
    normSq (-x) y z = normSq x y z := by
  unfold normSq
  rw [Int.neg_mul_neg]

-- ===========================================================================
-- WITNESSED round trips: concrete integer points on the R = 1000 sphere.
-- Each triple satisfies x*x + y*y + z*z = 1000000 exactly (decide).
-- These stand in for catalog directions pre-rounded onto the render sphere.
-- ===========================================================================

/-- Witness: the +x pole (a star on the vernal-equinox axis). -/
theorem round_trip_pole_x : normSq 1000 0 0 = radiusSq := by decide

/-- Witness: 600² + 800² + 0² = 360000 + 640000 = 1000000. -/
theorem round_trip_600_800 : normSq 600 800 0 = radiusSq := by decide

/-- Witness: a genuinely 3-D integer point on the sphere.
    360² + 480² + 800² = 129600 + 230400 + 640000 = 1000000. -/
theorem round_trip_360_480_800 : normSq 360 480 800 = radiusSq := by decide

/-- Witness: the antipode of the previous point is also on the sphere. -/
theorem round_trip_antipode : normSq (-360) (-480) (-800) = radiusSq := by decide

end CelestialCoordinates
end Gnosis
