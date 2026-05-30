namespace Gnosis
namespace OpticalShading

/-!
# Optical shading — the math the Earth water/atmosphere shader implements

Init-only (no Mathlib): everything is over scaled integers with `omega`/`decide`
and core `Int` monotonicity lemmas. We prove the STRUCTURAL guarantees the new
`house-renderer` water program relies on, so the GLSL is backed by theorems:

* **Fresnel–Schlick grazing**: the rim term `(1 − cosθ)^5` is brightest at grazing
  (cosθ → 0) and monotone in the viewing angle — the planet's limb glows, the
  sub-camera point does not (`rim_monotone_decreasing`, `rim_grazing_max`).
* **Specular reflection** `r = 2(n·l)n − l` preserves length when `n` is a unit
  normal, so the sun-glint sits on a true mirror direction (`refl_preserves_norm`).
* **Aerial perspective** fog is monotone in distance and saturates (bounded), so
  the horizon haze only ever grows with depth and never overshoots (`fog_monotone`,
  `fog_bounded`).

cosθ and fog are scaled to `SCALE = 1000` (i.e. value/1000 ∈ [0,1]). Proven, not
witnessed, except the concrete-angle samples (`decide`).
-/

/-- Fixed-point scale: a unit interval [0,1] is the integers [0, SCALE]. -/
def SCALE : Int := 1000

/-- `x^5` written as an explicit product so monotonicity needs only core
`Int.mul_le_mul_of_nonneg_*` (no `pow` lemmas, no Mathlib). -/
def mul5 (x : Int) : Int := x * x * x * x * x

/-- `x ↦ x^5` is monotone on the nonnegatives — the engine of Fresnel grazing. -/
theorem mul5_mono {a b : Int} (ha : 0 ≤ a) (hab : a ≤ b) : mul5 a ≤ mul5 b := by
  unfold mul5
  have hb : 0 ≤ b := Int.le_trans ha hab
  have hbb : 0 ≤ b * b := Int.mul_nonneg hb hb
  have hbbb : 0 ≤ b * b * b := Int.mul_nonneg hbb hb
  have hbbbb : 0 ≤ b * b * b * b := Int.mul_nonneg hbbb hb
  have s2 : a * a ≤ b * b :=
    Int.le_trans (Int.mul_le_mul_of_nonneg_right hab ha)
             (Int.mul_le_mul_of_nonneg_left hab hb)
  have s3 : a * a * a ≤ b * b * b :=
    Int.le_trans (Int.mul_le_mul_of_nonneg_right s2 ha)
             (Int.mul_le_mul_of_nonneg_left hab hbb)
  have s4 : a * a * a * a ≤ b * b * b * b :=
    Int.le_trans (Int.mul_le_mul_of_nonneg_right s3 ha)
             (Int.mul_le_mul_of_nonneg_left hab hbbb)
  exact Int.le_trans (Int.mul_le_mul_of_nonneg_right s4 ha)
                 (Int.mul_le_mul_of_nonneg_left hab hbbbb)

/-- Fresnel rim weight at scaled cosine `c = cosθ·SCALE ∈ [0, SCALE]`:
`(1 − cosθ)^5` scaled, i.e. `(SCALE − c)^5`. -/
def rim (c : Int) : Int := mul5 (SCALE - c)

/-- **Grazing monotonicity.** As the view approaches grazing (cosθ decreasing,
`c` decreasing) the rim only brightens: for `0 ≤ c1 ≤ c2 ≤ SCALE`, `rim c2 ≤ rim c1`. -/
theorem rim_monotone_decreasing {c1 c2 : Int}
    (_h1 : 0 ≤ c1) (h2 : c2 ≤ SCALE) (hle : c1 ≤ c2) : rim c2 ≤ rim c1 := by
  unfold rim
  exact mul5_mono (by omega) (by omega)

/-- **Grazing is the maximum.** The limb (`c = 0`, cosθ = 0) is the brightest rim. -/
theorem rim_grazing_max {c : Int} (h0 : 0 ≤ c) (h1 : c ≤ SCALE) : rim c ≤ rim 0 :=
  rim_monotone_decreasing (by omega) h1 h0

-- Concrete samples (decide): head-on (c=SCALE) is dark; grazing (c=0) is full.
example : rim SCALE = 0 := by decide
example : rim 0 = mul5 SCALE := by decide
example : rim 900 ≤ rim 100 := by decide   -- nearer grazing (c=100) brighter

/-! ## Specular reflection preserves length (the sun-glint mirror direction)

`r = 2(n·l)n − l`. With `d = n·l` and a UNIT normal (`n·n = 1`),
`r·r = 4 d² (n·n) − 4 d² + l·l = l·l`. We carry the dot products as integers
(`d = n·l`, `ll = l·l`) so the identity is exact in `Int`. -/

/-- `|r|²` for the reflected ray, in terms of `d = n·l`, the unit-normal factor
`nn = n·n`, and `ll = l·l`. -/
def reflNormSq (d nn ll : Int) : Int := 4 * (d * d) * nn - 4 * (d * d) + ll

/-- **Reflection is an isometry about a unit normal**: `|r|² = |l|²` when `n·n = 1`.
So the glint reflects the sun without changing intensity-by-geometry. -/
theorem refl_preserves_norm (d ll : Int) : reflNormSq d 1 ll = ll := by
  unfold reflNormSq
  simp only [Int.mul_one]
  omega

/-! ## Aerial perspective fog — monotone in distance, saturating (bounded)

The shader tints the far terrain by an accumulated-haze factor that grows with
distance and saturates at full tint. We model it as the saturating ramp
`fog d = min(SCALE, RATE·d)` (the discrete analog of `1 − e^{−k d}`): provably
monotone and bounded — the limb haze only deepens with depth and never overshoots. -/

/-- Haze accumulation per unit distance (scaled). -/
def RATE : Int := 5

/-- Accumulated aerial-perspective tint at distance `d` (scaled to [0, SCALE]). -/
def fog (d : Int) : Int := if RATE * d < SCALE then RATE * d else SCALE

/-- **Monotone in distance**: farther terrain is never less hazed. -/
theorem fog_monotone {d1 d2 : Int} (hle : d1 ≤ d2) : fog d1 ≤ fog d2 := by
  unfold fog RATE SCALE
  split <;> split <;> omega

/-- **Bounded**: the tint never exceeds full saturation `SCALE`. -/
theorem fog_bounded (d : Int) : fog d ≤ SCALE := by
  unfold fog RATE SCALE
  split <;> omega

-- Samples: no haze at zero distance, saturated far away.
example : fog 0 = 0 := by decide
example : fog 1000 = SCALE := by decide

end OpticalShading
end Gnosis
