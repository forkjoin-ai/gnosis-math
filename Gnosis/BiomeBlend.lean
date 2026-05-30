import Init

namespace Gnosis
namespace BiomeBlend

/-!
# Biome Blend (monster-studio Earth, Phase 2)

Backs blending a biome hue into lowland terrain color, fading the biome
contribution out with elevation so that highland / rock / snow are left
untouched.

All quantities are scaled INTEGERS (fixed-point), `SCALE = 1000`.
Elevation `e` is in metres. The biome blend `weight e` starts at `W0`
at sea level (and below) and ramps LINEARLY to `0` at the highland
threshold `H`, staying exactly `0` for `e ≥ H`.

The renderer mixes a base terrain colour `c` with a biome colour `b`:

  `blend c b e = ((SCALE - weight e) * c + weight e * b) / SCALE`

which is a convex combination weighted by `weight e / SCALE`.
-/

/-- Fixed-point scale. -/
def SCALE : Int := 1000

/-- Biome blend weight at sea level (out of `SCALE`). -/
def W0 : Int := 450

/-- Highland threshold (metres): at/above this the biome is not blended. -/
def H : Int := 1400

/-- Biome blend weight at elevation `e` (metres).
    `W0` at/below sea level, linear ramp to `0` at `H`, and exactly `0`
    for `e ≥ H`. Uses integer (e)division by the literal `H`. -/
def weight (e : Int) : Int :=
  if e ≤ 0 then W0
  else if H ≤ e then 0
  else W0 - (W0 * e) / H

/-- The weight is never negative. -/
theorem weight_nonneg (e : Int) : 0 ≤ weight e := by
  unfold weight W0 H
  split
  · omega
  · split
    · omega
    · omega

/-- The weight never exceeds the sea-level weight `W0`. -/
theorem weight_le_W0 (e : Int) : weight e ≤ W0 := by
  unfold weight W0 H
  split
  · omega
  · split
    · omega
    · omega

/-- The biome fades as you climb: higher elevation never increases the weight. -/
theorem weight_monotone_decreasing (e1 e2 : Int) :
    e1 ≤ e2 → weight e2 ≤ weight e1 := by
  intro h
  unfold weight W0 H
  split
  · split
    · omega
    · split <;> omega
  · split
    · split
      · omega
      · split <;> omega
    · split
      · omega
      · split <;> omega

/-- Highland is untouched: at or above the threshold the weight is exactly `0`. -/
theorem weight_zero_above (e : Int) : H ≤ e → weight e = 0 := by
  intro h
  unfold weight W0 H at *
  split <;> (try split) <;> omega

/-- Convex blend of base colour `c` and biome colour `b` at elevation `e`. -/
def blend (c b e : Int) : Int :=
  ((SCALE - weight e) * c + weight e * b) / SCALE

/-- Gamut preservation (lower bound): the blend output is non-negative
    whenever the inputs are in `[0, SCALE]`. -/
theorem blend_nonneg (c b e : Int)
    (hc : 0 ≤ c) (hb : 0 ≤ b) : 0 ≤ blend c b e := by
  unfold blend
  have hw0 : 0 ≤ weight e := weight_nonneg e
  have hwS : weight e ≤ SCALE := by
    have := weight_le_W0 e
    unfold W0 SCALE at *
    omega
  have h1 : 0 ≤ (SCALE - weight e) * c :=
    Int.mul_nonneg (by omega) hc
  have h2 : 0 ≤ weight e * b :=
    Int.mul_nonneg hw0 hb
  have hnum : 0 ≤ (SCALE - weight e) * c + weight e * b := by omega
  exact Int.ediv_nonneg hnum (by unfold SCALE; omega)

/-- Gamut preservation (upper bound): the blend output stays at or below
    `SCALE` whenever the inputs are in `[0, SCALE]`. -/
theorem blend_le_SCALE (c b e : Int)
    (hc : c ≤ SCALE) (hb : b ≤ SCALE)
    (_hc0 : 0 ≤ c) (_hb0 : 0 ≤ b) : blend c b e ≤ SCALE := by
  unfold blend
  have hw0 : 0 ≤ weight e := weight_nonneg e
  have hwS : weight e ≤ SCALE := by
    have := weight_le_W0 e
    unfold W0 SCALE at *
    omega
  have h1 : (SCALE - weight e) * c ≤ (SCALE - weight e) * SCALE :=
    Int.mul_le_mul_of_nonneg_left hc (by omega)
  have h2 : weight e * b ≤ weight e * SCALE :=
    Int.mul_le_mul_of_nonneg_left hb hw0
  have hdist : (SCALE - weight e) * SCALE + weight e * SCALE = SCALE * SCALE := by
    rw [← Int.add_mul]
    congr 1
    omega
  have hnum : (SCALE - weight e) * c + weight e * b ≤ SCALE * SCALE := by omega
  have hS : (0 : Int) < SCALE := by unfold SCALE; omega
  have hdiv : ((SCALE - weight e) * c + weight e * b) / SCALE
      ≤ (SCALE * SCALE) / SCALE := Int.ediv_le_ediv hS hnum
  have hrw : (SCALE * SCALE) / SCALE = SCALE := by unfold SCALE; decide
  omega

/-- No biome tint on highland: at or above the threshold the blend
    returns the base colour `c` exactly. -/
theorem blend_highland_identity (c b e : Int) :
    H ≤ e → blend c b e = c := by
  intro h
  unfold blend
  rw [weight_zero_above e h]
  simp only [Int.sub_zero, Int.zero_mul, Int.add_zero]
  rw [Int.mul_ediv_cancel_left c (by unfold SCALE; omega)]

/-- Concrete gamut witnesses (lower + upper bound at sample points). -/
example : 0 ≤ blend 0 0 0 ∧ blend 0 0 0 ≤ SCALE := by decide
example : 0 ≤ blend 1000 0 0 ∧ blend 1000 0 0 ≤ SCALE := by decide
example : 0 ≤ blend 200 800 700 ∧ blend 200 800 700 ≤ SCALE := by decide
example : 0 ≤ blend 1000 1000 1400 ∧ blend 1000 1000 1400 ≤ SCALE := by decide
example : blend 600 200 2000 = 600 := by decide

end BiomeBlend
end Gnosis
