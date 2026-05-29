namespace Gnosis
namespace ZoomLODGate

/-!
# Zoom LOD Gate — "no bacteria from space"

Spec for the monster-studio living-globe LOD
(`worldsim-viewport-lod.ts computeViewportCulling`, `ANGULAR_FLOOR`). An
organism is rendered/simulated only when its apparent angular size clears a
floor: `α = (charLen / dist) · zoom ≥ α_min`. To stay Init-only and
division-free we cross-multiply (all quantities positive): the angular floor
`α_min ≈ 5·10⁻⁴ rad` has inverse `FLOOR_INV = 1/α_min ≈ 2000`, so the organism
is **visible iff `dist ≤ FLOOR_INV · charLen · zoom`**.

This makes the gate a single, monotone, well-ordered threshold:
* closer is never worse (visibility is downward-closed in distance);
* larger organisms are visible from farther (size ordering);
* so each size-class has ONE first-visible distance — from orbit you see neither
  bacteria nor a single megafauna (only aggregate biomes); megafauna appear at
  low altitude, animals at ground, bacteria only under the microscope.

`omega` for distance/scaling monotonicity; `decide` witnesses for the ladder.
-/

/-- Inverse angular floor: `1 / α_min`, `α_min ≈ 5·10⁻⁴ rad` (≈ 1 px). -/
def FLOOR_INV : Int := 2000

/-- Visible iff the apparent size clears the floor:
`dist ≤ FLOOR_INV · charLen · zoom`. `charLen` is the organism's characteristic
length, `zoom` the camera zoom factor, `dist` the camera distance — all > 0,
same length unit (we use microns in the witnesses). -/
def visible (charLen dist zoom : Int) : Prop := dist ≤ FLOOR_INV * (charLen * zoom)

instance (c d z : Int) : Decidable (visible c d z) := by unfold visible; infer_instance

/-- The cull distance is exactly `FLOOR_INV · charLen · zoom`: a single,
well-ordered threshold per organism (definitional). -/
theorem first_visible_threshold (charLen dist zoom : Int) :
    visible charLen dist zoom ↔ dist ≤ FLOOR_INV * (charLen * zoom) := Iff.rfl

/-- **Distance-monotone (downward-closed).** If an organism is visible at some
distance, it stays visible everywhere closer — zooming in never hides what was
already shown. -/
theorem closer_stays_visible (charLen d1 d2 zoom : Int)
    (hle : d1 ≤ d2) (hvis : visible charLen d2 zoom) :
    visible charLen d1 zoom := by
  unfold visible at *
  omega

/-- **Far enough ⇒ culled.** Beyond the threshold the organism sleeps. -/
theorem beyond_threshold_culled (charLen dist zoom : Int)
    (h : FLOOR_INV * (charLen * zoom) < dist) : ¬ visible charLen dist zoom := by
  unfold visible
  omega

/-- **Size ordering.** At the same distance and zoom, a larger organism is
visible whenever a smaller one is (more, never fewer, big things on screen).
Uses `charLen₁·zoom ≤ charLen₂·zoom` for `zoom ≥ 0`. -/
theorem bigger_visible (c1 c2 dist zoom : Int)
    (hsize : c1 ≤ c2) (hz : 0 ≤ zoom) (hvis : visible c1 dist zoom) :
    visible c2 dist zoom := by
  unfold visible FLOOR_INV at *
  have hmul : c1 * zoom ≤ c2 * zoom := Int.mul_le_mul_of_nonneg_right hsize hz
  -- 2000·(c1·zoom) ≤ 2000·(c2·zoom) is linear scaling of hmul; omega.
  omega

/-! ## The ladder (decide) — char. lengths and distance in microns (µm), zoom = 1

bacteria ≈ 1 µm, animal ≈ 1e6 µm (1 m), megafauna ≈ 1e7 µm (10 m).
orbit dist ≈ 1e13 µm (1e7 m), low altitude ≈ 5e9 µm (5 km), ground ≈ 1e6 µm
(1 m), microscope ≈ 1 µm. visible iff dist ≤ 2000·charLen. -/

-- From orbit (1e13 µm): NOTHING individual — neither megafauna nor bacteria
-- (you see aggregate biomes, not single organisms).
example : ¬ visible 10_000_000 10_000_000_000_000 1 := by decide   -- megafauna: culled
example : ¬ visible 1 10_000_000_000_000 1 := by decide            -- bacteria: culled
-- Low altitude (5e9 µm ≈ 5 km): megafauna appear, bacteria still gone.
example : visible 10_000_000 5_000_000_000 1 := by decide          -- megafauna: shown
example : ¬ visible 1 5_000_000_000 1 := by decide                 -- bacteria: gone
-- Ground (1e6 µm ≈ 1 m): a 1-m animal is visible.
example : visible 1_000_000 1_000_000 1 := by decide
-- Microscope (1 µm): bacteria finally appear.
example : visible 1 1 1 := by decide

end ZoomLODGate
end Gnosis
