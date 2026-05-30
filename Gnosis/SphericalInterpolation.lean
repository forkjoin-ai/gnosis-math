namespace Gnosis
namespace SphericalInterpolation

/-!
# Spherical interpolation — the math behind the Earth camera `flyTo` tween

Init-only. Two guarantees the orbital fly-to relies on:

* **Shortest-arc azimuth** — when gliding from one longitude/azimuth to another, the
  camera must take the SHORT way around the circle, never spin >180°. We wrap the raw
  angle delta into `[−π, π)` and prove (a) the result is bounded by π in magnitude and
  (b) it is the same angle modulo a full turn (`wrap_bounded_*`, `wrap_same_angle`).
  Fully proven by `omega` (it reasons about `%` by a literal modulus).

* **Smoothstep easing** `e(t) = 3t² − 2t³` — the ease curve hits the endpoints exactly
  (no overshoot at start/end) and is monotone (the camera never reverses mid-glide).
  Scaled to a resolution-10 table (`smooth10 t = 30t² − 2t³`, mapping `t∈[0,10]` →
  `[0,1000]`); endpoints + monotonicity are WITNESSED on the table by `decide` (the
  renderer uses the continuous `3t²−2t³`).

Angles are scaled milli-radians: `PI = 3141`, `TAU = 2·PI = 6282`.
-/

def PI : Int := 3141
def TAU : Int := 6282   -- 2·PI exactly

/-- Wrap a raw angle delta into `(−PI, PI]` — the shortest signed arc. `Int.emod` by
the positive literal `TAU` lands in `[0, TAU)`, so the shifted-and-unshifted result is
in `[−PI, PI)`. -/
def wrapDelta (d : Int) : Int := (d + PI) % TAU - PI

/-- **Bounded below**: the shortest arc never undershoots −π. -/
theorem wrap_bounded_lo (d : Int) : -PI ≤ wrapDelta d := by
  unfold wrapDelta PI TAU
  omega

/-- **Bounded above**: the shortest arc never exceeds +π (so |delta| ≤ π — never the
long way around). -/
theorem wrap_bounded_hi (d : Int) : wrapDelta d < PI := by
  unfold wrapDelta PI TAU
  omega

/-- **Same angle**: the wrapped delta differs from the raw delta by a whole number of
full turns — it points at the identical azimuth, just chosen minimally. -/
theorem wrap_same_angle (d : Int) : (wrapDelta d - d) % TAU = 0 := by
  unfold wrapDelta PI TAU
  omega

-- Samples: a +350° request wraps to −10° (short way); −350° wraps to +10°.
-- (350° ≈ 6109 mrad, 10° ≈ 175 mrad.)
example : wrapDelta 6109 = -173 := by decide   -- nearly a full turn → small negative
example : wrapDelta 3000 = 3000 := by decide    -- already short, unchanged
example : wrapDelta 3141 = -3141 := by decide   -- exactly π is the boundary → −π
example : wrapDelta 0 = 0 := by decide

/-! ## Smoothstep easing table (resolution 10, witnessed)

`smooth10 t = 30 t² − 2 t³` maps `t ∈ [0,10]` to `[0,1000]` (it is `1000·e(t/10)` for
`e(x)=3x²−2x³`). Endpoints, range, and monotonicity are witnessed by `decide`. -/

def smooth10 (t : Int) : Int := 30 * t * t - 2 * t * t * t

-- Endpoints: e(0)=0, e(1)=1 — the glide starts and ends exactly on the targets.
example : smooth10 0 = 0 := by decide
example : smooth10 10 = 1000 := by decide
-- Symmetric midpoint e(0.5)=0.5.
example : smooth10 5 = 500 := by decide
-- Monotone across the table — the camera distance/angle only advances, never reverses.
example : smooth10 0 ≤ smooth10 1 := by decide
example : smooth10 1 ≤ smooth10 2 := by decide
example : smooth10 2 ≤ smooth10 3 := by decide
example : smooth10 3 ≤ smooth10 4 := by decide
example : smooth10 4 ≤ smooth10 5 := by decide
example : smooth10 5 ≤ smooth10 6 := by decide
example : smooth10 6 ≤ smooth10 7 := by decide
example : smooth10 7 ≤ smooth10 8 := by decide
example : smooth10 8 ≤ smooth10 9 := by decide
example : smooth10 9 ≤ smooth10 10 := by decide
-- In range [0,1000] at every table point (no overshoot).
example : 0 ≤ smooth10 3 ∧ smooth10 3 ≤ 1000 := by decide
example : 0 ≤ smooth10 7 ∧ smooth10 7 ≤ 1000 := by decide

end SphericalInterpolation
end Gnosis
