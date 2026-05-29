namespace Gnosis
namespace WeatherDynamics

/-!
# Weather Dynamics — conservation laws for the atmosphere

The repo norm: weather must be Lean-proven before it is rendered
(`worldsim-weather.ts stepWeather`). Init-only (no Mathlib), so we prove the
**structural conservation core** over integers — the invariants a correct
discrete weather step must satisfy regardless of the continuous PDE:

* **Advection conserves mass** — moisture transported between cells by wind is
  neither created nor destroyed (the per-cell flux terms telescope to zero on a
  closed ring).
* **Flux balance (divergence-free)** — on a closed sphere every flux leaving a
  cell enters its neighbour, so the net divergence is zero.
* **Precipitation is a monotone threshold** — rain falls only above the
  condensation threshold, and more humidity never means less rain.

Proved by `omega` (linear identities on the cell totals) + `decide` witnesses.
The continuous advection PDE is approximated/tested in TS, not proved over ℝ.
-/

/-! ## Advection mass conservation (closed 3-cell ring) -/

/-- A discrete advection step on a closed ring moves flux `fᵢ` from cell `i` to
cell `i+1` (cyclic). New mass `mᵢ' = mᵢ − fᵢ + f₍ᵢ₋₁₎`. **Total mass is
conserved**: the flux terms cancel cyclically. -/
theorem advection_conserves_mass_3 (m0 m1 m2 f0 f1 f2 : Int) :
    ((m0 - f0 + f2) + (m1 - f1 + f0) + (m2 - f2 + f1)) = m0 + m1 + m2 := by
  omega

/-- Same on a 4-cell ring — conservation is independent of resolution. -/
theorem advection_conserves_mass_4 (m0 m1 m2 m3 f0 f1 f2 f3 : Int) :
    ((m0 - f0 + f3) + (m1 - f1 + f0) + (m2 - f2 + f1) + (m3 - f3 + f2))
      = m0 + m1 + m2 + m3 := by
  omega

/-- **Flux balance / divergence-free.** Every flux leaving a cell enters its
neighbour, so the signed net flux around the closed ring is zero. -/
theorem flux_divergence_free_3 (f0 f1 f2 : Int) :
    (f0 - f1) + (f1 - f2) + (f2 - f0) = 0 := by
  omega

/-! ## Precipitation: monotone condensation threshold -/

/-- Precipitation: humidity above the condensation `threshold` rains out; below
it, nothing falls. -/
def precip (humidity threshold : Int) : Int :=
  if humidity > threshold then humidity - threshold else 0

/-- Below/at the threshold, no rain. -/
theorem precip_dry (humidity threshold : Int) (h : humidity ≤ threshold) :
    precip humidity threshold = 0 := by
  unfold precip
  split <;> omega

/-- Above the threshold, rain equals the excess humidity. -/
theorem precip_excess (humidity threshold : Int) (h : threshold < humidity) :
    precip humidity threshold = humidity - threshold := by
  unfold precip
  split <;> omega

/-- **Monotone**: more humidity never produces less rain. -/
theorem precip_monotone (h1 h2 threshold : Int) (h : h1 ≤ h2) :
    precip h1 threshold ≤ precip h2 threshold := by
  unfold precip
  split <;> split <;> omega

/-- Precipitation is never negative (rain can't be undone). -/
theorem precip_nonneg (humidity threshold : Int) : 0 ≤ precip humidity threshold := by
  unfold precip
  split <;> omega

-- Witnesses.
example : precip 70 50 = 20 := by decide   -- 20 above threshold rains out
example : precip 40 50 = 0 := by decide    -- below threshold: dry
example : precip 50 50 = 0 := by decide    -- at threshold: dry

end WeatherDynamics
end Gnosis
