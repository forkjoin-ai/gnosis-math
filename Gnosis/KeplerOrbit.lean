namespace Gnosis
namespace KeplerOrbit

/-!
# Kepler Orbit — two-body orbital math for the True Solar System

Repo norm (same as `OceanDynamics` / `WeatherDynamics`): the orbits the
renderer draws must be Lean-proven before they are rendered. Init-only (no
Mathlib), so we prove the **structural core** of the two-body problem over the
integers, modelling the transcendental `sin`/`cos` abstractly by their defining
bound `|·| ≤ 1` (scaled) rather than over ℝ.

Everything is **fixed-point**: a scale `S` represents `1.0`, so a value `v : Int`
denotes `v / S`. Eccentricity `e` is an integer with `0 ≤ e < S` (`0 ≤ e < 1`),
and `sinE`, `cosE` are integers with `-S ≤ · ≤ S` (`|sin|, |cos| ≤ 1`).

Proved:

* **Kepler's equation `M = E − e·sin E` is strictly monotone in `E`** for
  `0 ≤ e < 1`, hence **injective**: each mean anomaly `M` has at most one
  eccentric-anomaly solution `E`. The transcendental "chord of `sin` is bounded
  by the gap" fact enters honestly as a clearly-labelled Lipschitz hypothesis
  (it holds for the real `sin` exactly when `e < 1`).
* **Orbit radius `r = a(1 − e·cos E)` is bounded in `[a(1−e), a(1+e)]`** —
  perihelion / aphelion. Proved from `−1 ≤ cos E ≤ 1`, `0 ≤ e`, `a ≥ 0` using
  only core `Int` monotonicity lemmas.
* **Kepler's third law** `T² = k·a³` as exact integer algebraic identities
  (cube scaling and the cross-multiplied ratio).

What genuinely needs ℝ (existence of the solution `E`, analytic `sin`/`cos`) is
supplied as **clearly-labelled hypotheses**, never faked. Closed with `omega`,
core `Int` lemmas, and `decide` — zero `sorry`.
-/

/-! ## Kepler's equation: uniqueness via strict monotonicity -/

/-- Kepler's equation, mean anomaly from eccentric anomaly (fixed-point):
`M·S = E·S − e·sinE`, i.e. `M = E − e·sin E` after dividing by the scale `S`.
Kept unscaled-on-the-left so the product `e·sinE` stays integral. -/
def meanAnomalyScaled (S e sinE Eanom : Int) : Int := Eanom * S - e * sinE

/-- **Strict monotonicity of Kepler's equation (the uniqueness core).**

If `Ea < Eb` (eccentric anomaly increases), then `M(Ea) < M(Eb)` for any
eccentricity `0 ≤ e < S` (`0 ≤ e < 1`). The transcendental fact "the chord of
`sin` over the interval is bounded by `e` times the gap" enters honestly as the
hypothesis `hLip : e * (sinEb - sinEa) < (Eb - Ea) * S` — the contraction bound
that holds for the real `sin` exactly when `e < 1`. Conclusion: `M` strictly
increases. -/
theorem kepler_strict_mono
    (S e sinEa sinEb Ea Eb : Int)
    (hLip : e * (sinEb - sinEa) < (Eb - Ea) * S) :
    meanAnomalyScaled S e sinEa Ea < meanAnomalyScaled S e sinEb Eb := by
  unfold meanAnomalyScaled
  have h1 : e * (sinEb - sinEa) = e * sinEb - e * sinEa := by rw [Int.mul_sub]
  have h2 : (Eb - Ea) * S = Eb * S - Ea * S := by rw [Int.sub_mul]
  omega

/-- **Uniqueness of the solution (strictly increasing ⇒ injective).** Two
eccentric anomalies producing the same mean anomaly under Kepler's equation must
be equal, given the contraction bound in both orderings. This is the fact the
solver relies on: Newton iteration converges to *the* root, not one of many. -/
theorem kepler_unique
    (S e sinEa sinEb Ea Eb : Int)
    (hEq : meanAnomalyScaled S e sinEa Ea = meanAnomalyScaled S e sinEb Eb)
    (hLipAB : e * (sinEb - sinEa) < (Eb - Ea) * S)
    (hLipBA : e * (sinEa - sinEb) < (Ea - Eb) * S) :
    Ea = Eb := by
  rcases Int.lt_trichotomy Ea Eb with hlt | heq | hgt
  · have := kepler_strict_mono S e sinEa sinEb Ea Eb hLipAB
    rw [hEq] at this; exact absurd this (Int.lt_irrefl _)
  · exact heq
  · have := kepler_strict_mono S e sinEb sinEa Eb Ea hLipBA
    rw [hEq] at this; exact absurd this (Int.lt_irrefl _)

/-! ## Orbit radius bounded by perihelion / aphelion -/

/-- Orbit radius, fixed-point at scale `S²`: `r = a(1 − e·cos E)` becomes
`radiusScaled = a·(S·S − e·cosE)` (since `1 ↦ S`, `e·cosE` is at scale `S²`). -/
def radiusScaled (a S e cosE : Int) : Int := a * (S * S - e * cosE)

/-- **Radius lower bound (perihelion).** With `a ≥ 0`, `0 ≤ e`, `cos E ≤ S`
(`cos E ≤ 1`), the radius is at least `a·S·(S − e) = a(1 − e)` (scale `S²`). -/
theorem radius_ge_perihelion
    (a S e cosE : Int)
    (ha : 0 ≤ a) (he0 : 0 ≤ e)
    (hcos : cosE ≤ S) :
    a * (S * (S - e)) ≤ radiusScaled a S e cosE := by
  unfold radiusScaled
  -- e·cosE ≤ e·S  (mult cosE ≤ S by e ≥ 0), so S·S − e·cosE ≥ S·S − e·S = S(S−e)
  have hprod : e * cosE ≤ e * S := Int.mul_le_mul_of_nonneg_left hcos he0
  have hexp : S * (S - e) = S * S - e * S := by
    rw [Int.mul_sub, Int.mul_comm S e]
  have hinner : S * (S - e) ≤ S * S - e * cosE := by
    rw [hexp]; omega
  exact Int.mul_le_mul_of_nonneg_left hinner ha

/-- **Radius upper bound (aphelion).** With `a ≥ 0`, `0 ≤ e`, `-S ≤ cos E`
(`-1 ≤ cos E`), the radius is at most `a·S·(S + e) = a(1 + e)` (scale `S²`). -/
theorem radius_le_aphelion
    (a S e cosE : Int)
    (ha : 0 ≤ a) (he0 : 0 ≤ e)
    (hcos : -S ≤ cosE) :
    radiusScaled a S e cosE ≤ a * (S * (S + e)) := by
  unfold radiusScaled
  -- e·(−S) ≤ e·cosE, i.e. −(e·S) ≤ e·cosE, so S·S − e·cosE ≤ S·S + e·S = S(S+e)
  have hprod : e * (-S) ≤ e * cosE := Int.mul_le_mul_of_nonneg_left hcos he0
  have he1 : e * (-S) = -(e * S) := by rw [Int.mul_neg]
  have hexp : S * (S + e) = S * S + e * S := by
    rw [Int.mul_add, Int.mul_comm S e]
  have hinner : S * S - e * cosE ≤ S * (S + e) := by
    rw [hexp]; omega
  exact Int.mul_le_mul_of_nonneg_left hinner ha

/-- **Radius is bracketed by perihelion and aphelion.** The full
`r ∈ [a(1−e), a(1+e)]` statement the orbit renderer relies on. -/
theorem radius_bounds
    (a S e cosE : Int)
    (ha : 0 ≤ a) (he0 : 0 ≤ e)
    (hcosLo : -S ≤ cosE) (hcosHi : cosE ≤ S) :
    a * (S * (S - e)) ≤ radiusScaled a S e cosE ∧
      radiusScaled a S e cosE ≤ a * (S * (S + e)) :=
  ⟨radius_ge_perihelion a S e cosE ha he0 hcosHi,
   radius_le_aphelion a S e cosE ha he0 hcosLo⟩

/-- Perihelion radius is positive for a genuine ellipse (`a > 0`, `S > 0`,
`0 ≤ e < S`): the orbit never collapses through the focus. -/
theorem perihelion_pos
    (a S e : Int) (ha : 0 < a) (hS : 0 < S) (he : e < S) (_he0 : 0 ≤ e) :
    0 < a * (S * (S - e)) := by
  have h1 : 0 < S - e := by omega
  have h2 : 0 < S * (S - e) := Int.mul_pos hS h1
  exact Int.mul_pos ha h2

/-! ## Kepler's third law as an exact identity -/

/-- Kepler's third law: `T² = k·a³`, with `k = 4π²/(G·M_sun)`. Exact integer
form (the renderer carries `k` and `a` as fixed-point integers). -/
def periodSquared (k a : Int) : Int := k * (a * a * a)

/-- **Kepler's third law — cube scaling identity.** Doubling the semi-major
axis multiplies the squared period by `2³ = 8`. The form the renderer uses to
place an orbit from a reference orbit. -/
theorem keplers_third_scaling (k a : Int) :
    periodSquared k (2 * a) = 8 * periodSquared k a := by
  unfold periodSquared
  show k * ((2 * a) * (2 * a) * (2 * a)) = 8 * (k * (a * a * a))
  have h8 : (8 : Int) = 2 * 2 * 2 := by decide
  rw [h8]
  ac_rfl

/-- **Kepler's third law — ratio (cross-multiplied) identity.** For two bodies
sharing the constant `k`: `T₁²·a₂³ = T₂²·a₁³`. The form used to derive one
orbit's period from another's. -/
theorem keplers_third_ratio (k a1 a2 : Int) :
    periodSquared k a1 * (a2 * a2 * a2) = periodSquared k a2 * (a1 * a1 * a1) := by
  unfold periodSquared
  ac_rfl

-- Witnesses (scale S = 100, so 1.0 = 100; eccentricity e = 50 = 0.5).
-- Kepler's equation strictly increases from Ea=0 to Eb=100 (one full radian-ish
-- step), with a valid contraction bound:
example :
    meanAnomalyScaled 100 50 0 0 < meanAnomalyScaled 100 50 80 100 := by
  unfold meanAnomalyScaled; decide
-- Radius at cos E = +S (perihelion, r = a(1-e)) and cos E = -S (aphelion):
-- a = 1 (=100? use a=1 unscaled), S=100, e=50:
example : radiusScaled 1 100 50 100 = 5000 := by unfold radiusScaled; decide   -- a(S²−eS)=S²−eS=10000−5000
example : radiusScaled 1 100 50 (-100) = 15000 := by unfold radiusScaled; decide -- 10000+5000
-- Third-law cube scaling.
example : periodSquared 1 2 = 8 := by unfold periodSquared; decide
example : periodSquared 3 2 = 24 := by unfold periodSquared; decide

end KeplerOrbit
end Gnosis
