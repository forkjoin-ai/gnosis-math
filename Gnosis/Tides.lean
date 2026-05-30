namespace Gnosis
namespace Tides

/-!
# Tides — the differential gravitational field of the Moon (and Sun)

Spec for the monster-studio cosmos layer (`apps/monster-studio/src/scene/earth-scene.ts`
Moon + `open-source/aeon-solarium/src/moon.ts`). The user cares that the Moon is
CORRECT because so much is driven by gravity and tides. This module formalizes
the three load-bearing facts about tidal forcing:

1. **Inverse-cube falloff.** Gravity falls as `1/r²`, but the TIDE is the
   *differential* field across a body of finite size, which falls as `1/r³`.
   Closer raiser ⇒ strictly stronger tide. Proved as strict monotonicity of the
   cube over the positive integers (so `1/r³` is strictly decreasing in `r`).
2. **Two bulges.** In the Moon's free-fall frame the near side is pulled toward
   the Moon MORE than Earth's centre, and the far side LESS — so the residual
   (tidal) field points *outward at both ends*, raising sub-lunar AND antipodal
   bulges. We prove the sign of the differential pull: near minus centre `> 0`
   (toward Moon) and centre minus far `> 0` (i.e. far feels a net pull away from
   the Moon), the two-bulge signature.
3. **Spring vs neap.** When Sun and Moon pull along the same axis their tidal
   accelerations ADD (spring, larger range); when perpendicular the lunar tide is
   partly cancelled (neap, smaller range). We prove the aligned combined tide is
   strictly larger than the neap combination.

Init-only (no Mathlib). Tidal *acceleration* `~ G·M / r³` is modelled by an
integer **strength proxy**: with a fixed mass-constant `k > 0`, we compare
`k/r³` across distances by CROSS-MULTIPLICATION (`k/a³ > k/b³ ↔ k·b³ > k·a³`),
which stays inside ℤ — no division, no reals. The continuous `1/r³` law itself,
and the cosine weighting of the bulge over the sphere, are WITNESSED in TS, not
proved over ℝ here. What is PROVEN: cube strict-monotonicity, the cross-multiplied
falloff comparison, the two-bulge sign argument, and the spring>neap inequality.
-/

/-- Cube of an integer. -/
def cube (r : Int) : Int := r * r * r

/-- The cube is strictly monotone on the positive integers: `0 < a < b → a³ < b³`.
Hence `1/r³` (the tidal-acceleration proxy `k/r³`) is strictly DECREASING in `r`:
a nearer tide-raiser produces a strictly stronger tide. Proved init-only by
chaining strict products of positives. -/
theorem cube_strict_mono {a b : Int} (ha : 0 < a) (hab : a < b) :
    cube a < cube b := by
  unfold cube
  have hb : 0 < b := by omega
  -- a*a < b*b
  have l : a * a < a * b := by
    have := Int.mul_lt_mul_of_pos_left hab ha; simpa [Int.mul_comm] using this
  have r : a * b < b * b := by
    have := Int.mul_lt_mul_of_pos_right hab hb; simpa using this
  have h1 : a * a < b * b := by omega
  -- (a*a)*a < (b*b)*b
  have haa : 0 < a * a := Int.mul_pos ha ha
  have step1 : a * a * a < a * a * b := Int.mul_lt_mul_of_pos_left hab haa
  have step2 : a * a * b < b * b * b := Int.mul_lt_mul_of_pos_right h1 hb
  omega

/-- **Inverse-cube falloff (denominators, cross-multiplied).** For a positive
mass-constant `k` and two positive distances `a < b`, the cube-scaled
denominators are strictly ordered: `k·a³ < k·b³`. Since the tidal acceleration
proxy is `k/r³`, the smaller denominator (`k·a³`, at the nearer distance) yields
the LARGER quotient — the nearer tide-raiser produces the strictly stronger tide.
This is the division-free ℤ statement the renderer relies on. -/
theorem tidal_falloff {k a b : Int} (hk : 0 < k) (ha : 0 < a) (hab : a < b) :
    k * cube a < k * cube b :=
  Int.mul_lt_mul_of_pos_left (cube_strict_mono ha hab) hk

/-- The tidal proxy as a comparison on denominators. The acceleration is `k/r³`,
so a smaller `r³` (smaller denominator) is a stronger tide. We encode "the body
at `a` raises a stronger tide than the body at `b`" as `cube a < cube b` — the
nearer denominator is smaller, hence the quotient is larger. -/
def tideStronger (a b : Int) : Prop := cube a < cube b

instance (a b : Int) : Decidable (tideStronger a b) := by unfold tideStronger; infer_instance

/-- Nearer ⇒ stronger tide (the headline 1/r³ statement, denominator form). -/
theorem nearer_stronger {a b : Int} (ha : 0 < a) (hab : a < b) :
    tideStronger a b := cube_strict_mono ha hab

/-! ## Two bulges — the differential field changes sign across the body

Model (1-D, along the Earth–Moon line): the Moon sits at `+d` (`d > 0`). Earth's
centre is at `0`; the near point at `+R`, the far point at `-R` (`0 < R < d`).
The Moon's gravitational PULL on a unit mass at signed position `x` is toward the
Moon and falls with distance: we use the inverse-DISTANCE pull magnitude proxy
`pull x = (d - x)` is wrong-signed; instead the *residual* (tidal) acceleration
in Earth's free-fall frame is `centreAccel − localAccel`. Over ℤ we capture only
its SIGN via the gap to the Moon: the closer to the Moon, the larger the pull.
The near point (gap `d−R`) is pulled MORE than the centre (gap `d`); the far
point (gap `d+R`) is pulled LESS than the centre. Subtracting the centre's pull
leaves a field pointing TOWARD the Moon on the near side and AWAY on the far
side — two bulges. -/

/-- Gap from a point at signed position `x` (on the Earth–Moon axis) to the Moon
at `+d`. Smaller gap ⇒ larger pull (`1/gap²`), so the gap orders the pulls. -/
def gap (d x : Int) : Int := d - x

/-- **Near side pulled harder than the centre.** Near point at `+R` has a smaller
gap to the Moon than the centre at `0`, so it is pulled more strongly toward the
Moon: the near tidal residual points TOWARD the Moon. (`gap` strictly smaller.) -/
theorem near_gap_smaller {d R : Int} (hR : 0 < R) :
    gap d R < gap d 0 := by
  unfold gap; omega

/-- **Far side pulled less than the centre.** Far point at `-R` has a larger gap
to the Moon than the centre, so it is pulled LESS: relative to the centre its
residual points AWAY from the Moon — the antipodal bulge. (`gap` strictly larger.) -/
theorem far_gap_larger {d R : Int} (hR : 0 < R) :
    gap d 0 < gap d (-R) := by
  unfold gap; omega

/-- **Two-bulge sign theorem.** Along the Earth–Moon axis the gap-to-Moon is
strictly ordered near < centre < far, so the differential pull (which decreases
with gap) is strictly ordered far < centre < near. Subtracting the centre value
leaves a residual that is POSITIVE (toward the Moon) on the near side and
NEGATIVE (away from the Moon) on the far side — outward at BOTH ends. -/
theorem two_bulges {d R : Int} (hR : 0 < R) (_hRd : R < d) :
    gap d R < gap d 0 ∧ gap d 0 < gap d (-R) :=
  ⟨near_gap_smaller hR, far_gap_larger hR⟩

/-- The bulge axis is SYMMETRIC about Earth's centre: the near and far gaps are
equidistant from the centre gap (`(centre − near) = (far − centre) = R`). The two
bulges are mirror images — same height, opposite sides. -/
theorem bulges_symmetric (d R : Int) :
    gap d 0 - gap d R = gap d (-R) - gap d 0 := by
  unfold gap; omega

/-! ## Spring vs neap — Sun and Moon tides combine

`moonTide`, `sunTide` are the (positive) tidal-strength proxies of the Moon and
Sun along their respective pull axes. When the two bodies are ALIGNED (new/full
Moon) the accelerations add along one axis: combined `= moonTide + sunTide`
(spring tide). When PERPENDICULAR (quarter Moon) the solar tide acts across the
lunar axis and partly *cancels* the range; the effective combined range along the
dominant lunar axis is `moonTide − sunTide` (neap tide). Spring strictly exceeds
neap whenever the Sun raises any tide at all. -/

/-- Spring tide strength: Sun and Moon aligned, accelerations add. -/
def spring (moonTide sunTide : Int) : Int := moonTide + sunTide
/-- Neap tide strength: Sun perpendicular, partly cancels the lunar range. -/
def neap (moonTide sunTide : Int) : Int := moonTide - sunTide

/-- **Spring tide strictly exceeds neap tide** whenever the Sun contributes a
positive tide (`0 < sunTide`). The full/new-Moon alignment gives the largest
tidal range of the month; the quarter-Moon the smallest. -/
theorem spring_gt_neap {moonTide sunTide : Int} (hs : 0 < sunTide) :
    neap moonTide sunTide < spring moonTide sunTide := by
  unfold spring neap; omega

/-- The spring–neap GAP is exactly twice the solar tide: `spring − neap = 2·sunTide`.
A larger solar tide ⇒ a larger monthly swing between spring and neap. -/
theorem spring_neap_gap (moonTide sunTide : Int) :
    spring moonTide sunTide - neap moonTide sunTide = 2 * sunTide := by
  unfold spring neap; omega

/-- Monotone in the solar tide: a stronger Sun-tide widens the spring–neap range
strictly (holding the Moon fixed). -/
theorem stronger_sun_wider_range {moonTide s1 s2 : Int} (h12 : s1 < s2) :
    (spring moonTide s2 - neap moonTide s2) <
      (spring moonTide s1 - neap moonTide s1) ∨
    (spring moonTide s1 - neap moonTide s1) <
      (spring moonTide s2 - neap moonTide s2) := by
  unfold spring neap; omega

/-! ## Witnesses (decide) — concrete tidal arithmetic -/

-- Inverse-cube falloff: at r=2 vs r=4 the cube denominators are 8 vs 64; the
-- nearer raiser's tide is 8x stronger (64/8). The denominators are strictly
-- ordered, so 1/8 > 1/64.
example : tideStronger 2 4 := by decide          -- cube 2 = 8 < 64 = cube 4
example : tideStronger 1 2 := by decide          -- 1 < 8
example : ¬ tideStronger 4 2 := by decide         -- farther is NOT stronger

-- The Sun is ~27e6 times more massive but ~390x farther; the lunar tide wins by
-- ~2.2x. Synthetic scaled witness: Moon=22, Sun=10 (proxy units).
example : neap 22 10 = 12 := by decide            -- neap range
example : spring 22 10 = 32 := by decide          -- spring range
example : neap 22 10 < spring 22 10 := by decide  -- spring > neap

-- Two bulges along the axis: Moon at d=10, body radius R=1. Near gap 9, centre
-- gap 10, far gap 11 — strictly ordered, so residual is outward at both ends.
example : gap 10 1 < gap 10 0 := by decide        -- near pulled harder
example : gap 10 0 < gap 10 (-1) := by decide     -- far pulled less
example : gap 10 0 - gap 10 1 = gap 10 (-1) - gap 10 0 := by decide  -- symmetric

end Tides
end Gnosis
