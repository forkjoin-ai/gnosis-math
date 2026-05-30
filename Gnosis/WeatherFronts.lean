/-
  WeatherFronts.lean
  ==================

  Structural core for organized weather in the monster-studio Earth (Phase 4):
  fronts, cyclones, and the ITCZ as pressure-driven, geostrophically-steered
  flow.

  The geostrophic balance says the wind blows ALONG isobars (perpendicular to
  the pressure gradient), with a rotation sense set by the Coriolis force —
  opposite in the two hemispheres. From a pressure field alone, the discrete
  curl (vorticity) of the gradient must vanish: a gradient field carries no
  spurious circulation.

  We carry 2-D vectors as integer components (scaled units) and prove the
  STRUCTURAL/algebraic core. Continuum existence of the steered flow is
  deferred (millennium boundary; corpus convention) — here we certify the
  discrete identities the renderer relies on.

  Init-only, no Mathlib.
-/

namespace Gnosis
namespace WeatherFronts

/-- The 2-D dot product of integer-component vectors. -/
def dot (ax ay bx by_ : Int) : Int := ax * bx + ay * by_

/--
  `geostrophic_perp`: the geostrophic wind is PERPENDICULAR to the pressure
  gradient. Given a gradient `(gx, gy)`, the geostrophic wind is the 90°
  rotation `(-gy, gx)`. Their dot product is exactly zero: the wind blows
  along the isobars.
-/
theorem geostrophic_perp (gx gy : Int) :
    dot (-gy) gx gx gy = 0 := by
  unfold dot
  -- (-gy)*gx + gx*gy = -(gx*gy) + gx*gy ; rewrite so both terms share the atom gx*gy
  have h : (-gy) * gx = -(gx * gy) := by
    rw [Int.neg_mul, Int.mul_comm]
  rw [h]
  omega

/--
  The hemisphere-signed geostrophic rotation. `s = +1` in the Northern
  hemisphere, `s = -1` in the Southern. The wind is `(s*(-gy), s*gx)`.
-/
def windX (s gx gy : Int) : Int := s * (-gy)
def windY (s gx gy : Int) : Int := s * gx

/--
  `coriolis_sign`: the rotation SENSE flips by hemisphere. The Northern wind is
  the exact componentwise negation of the Southern wind.
-/
theorem coriolis_sign (gx gy : Int) :
    windX 1 gx gy = -(windX (-1) gx gy) ∧
    windY 1 gx gy = -(windY (-1) gx gy) := by
  unfold windX windY
  omega

/--
  `vorticity_conserved` (discrete): a closed 4-cell circulation sum telescopes
  to zero. The discrete curl of a gradient field vanishes — the pressure field
  alone produces no spurious vorticity.
-/
theorem vorticity_conserved (a b c d : Int) :
    (a - b) + (b - c) + (c - d) + (d - a) = 0 := by
  omega

end WeatherFronts
end Gnosis
