namespace Gnosis
namespace OceanDynamics

/-!
# Ocean Dynamics — conservation laws for shallow water

Repo norm (same as `WeatherDynamics`): water must be Lean-proven before it is
rendered. Init-only (no Mathlib), so we prove the **structural conservation
core** over integers — the invariants a correct discrete shallow-water /
sea-level step must satisfy regardless of the continuous PDE:

* **Mass (volume) conservation** — water redistributed between columns by
  inter-cell flux is neither created nor destroyed (flux terms telescope on a
  closed ring). This is the gate for any animated ocean surface.
* **Continuity (divergence-free flux)** — on a closed basin every flux leaving a
  column enters its neighbour, so net divergence is zero.
* **Tidal displacement is bounded** — the tide never exceeds its amplitude.
* **Wave height is a monotone, non-negative threshold of forcing** — calmer seas
  never produce taller waves; height is clamped at zero (no negative water).

Proved by `omega` (linear identities on column totals) + `decide` witnesses.
The continuous shallow-water PDE is approximated/tested in TS, not proved over ℝ.
-/

/-! ## Shallow-water mass (volume) conservation (closed ring of water columns) -/

/-- A discrete shallow-water step on a closed ring moves flux `fᵢ` from column
`i` to column `i+1` (cyclic). New column volume `hᵢ' = hᵢ − fᵢ + f₍ᵢ₋₁₎`.
**Total water volume is conserved**: the flux terms cancel cyclically. -/
theorem mass_conserved_3 (h0 h1 h2 f0 f1 f2 : Int) :
    ((h0 - f0 + f2) + (h1 - f1 + f0) + (h2 - f2 + f1)) = h0 + h1 + h2 := by
  omega

/-- Same on a 4-column basin — conservation is independent of resolution. -/
theorem mass_conserved_4 (h0 h1 h2 h3 f0 f1 f2 f3 : Int) :
    ((h0 - f0 + f3) + (h1 - f1 + f0) + (h2 - f2 + f1) + (h3 - f3 + f2))
      = h0 + h1 + h2 + h3 := by
  omega

/-- **Continuity / divergence-free.** Every flux leaving a column enters its
neighbour, so the signed net flux around the closed basin is zero. -/
theorem continuity_divergence_free_3 (f0 f1 f2 : Int) :
    (f0 - f1) + (f1 - f2) + (f2 - f0) = 0 := by
  omega

/-! ## Tides: displacement bounded by amplitude -/

/-- A two-phase tidal displacement: high tide `+amp`, low tide `−amp`. -/
def tide (amp phase : Int) : Int :=
  if phase ≥ 0 then amp else -amp

/-- **Tides are bounded**: the displacement never exceeds the amplitude either
way (sea level stays within `[−amp, amp]`). -/
theorem tide_bounded (amp phase : Int) (h : 0 ≤ amp) :
    -amp ≤ tide amp phase ∧ tide amp phase ≤ amp := by
  unfold tide
  split <;> omega

/-! ## Waves: monotone, non-negative height from forcing -/

/-- Wave height from wind/fetch `forcing`: positive forcing raises a wave;
non-positive forcing leaves a flat (zero-height) sea. Clamped — water height is
never negative. -/
def waveHeight (forcing : Int) : Int :=
  if forcing > 0 then forcing else 0

/-- Calm/negative forcing means a flat sea. -/
theorem wave_flat (forcing : Int) (h : forcing ≤ 0) :
    waveHeight forcing = 0 := by
  unfold waveHeight
  split <;> omega

/-- **Wave height is never negative** (no negative water column). -/
theorem wave_height_nonneg (forcing : Int) : 0 ≤ waveHeight forcing := by
  unfold waveHeight
  split <;> omega

/-- **Monotone**: stronger forcing never produces a shorter wave. -/
theorem wave_height_monotone (a b : Int) (h : a ≤ b) :
    waveHeight a ≤ waveHeight b := by
  unfold waveHeight
  split <;> split <;> omega

-- Witnesses.
example : tide 3 1 = 3 := by decide        -- high tide
example : tide 3 (-1) = -3 := by decide     -- low tide
example : waveHeight 5 = 5 := by decide     -- forced sea
example : waveHeight (-2) = 0 := by decide  -- calm sea is flat

end OceanDynamics
end Gnosis
