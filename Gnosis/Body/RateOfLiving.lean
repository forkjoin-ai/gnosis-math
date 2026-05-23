import Init
import Gnosis.Body.ConservationOfVitality

/-!
# The Rate of Living — why men die before women

A test of `Gnosis/Body/ConservationOfVitality.lean` against real numbers. If
vitality is a conserved budget (`totalVitality = rate * duration`), a higher burn
*rate* buys a shorter *life*. Men burn hotter and die sooner: the rate-of-living
hypothesis, which is exactly the conservation prediction.

**The frame matters.** In *absolute* calories the budget is NOT conserved — men
burn ~17% more over a lifetime, because they are bigger. The conserved quantity is
the **mass-specific** one (kcal per kg). With population-average figures:

| | mass-specific rate (kcal/kg/day) | lifespan (yr) | lifetime (kcal/kg) |
|---|---|---|---|
| men | 31.25 (= 2500/80) | 76 | 866,875 |
| women | 29.41 (= 2000/68) | 81 | 869,559 |

The lifetime per-kg budgets agree to **0.3%**. Men spend a fixed per-kg budget at a
higher rate over a shorter time; women lower and longer; the total is the same.
The three ratios cancel: `(TDEE 1.25) × (1/mass 0.85) × (lifespan 0.94) ≈ 1.00`.

## Honesty (this is illustrative, not a sole-cause claim)

The figures are rounded population averages and the fit is sensitive to them.
The rate-of-living hypothesis is *contested* (birds/bats live long at high
metabolism). And men dying ~5 years sooner is **multifactorial**: testosterone's
oxidative/immune cost, the "unguarded X" (XY has no backup allele where XX does),
and behaviour all contribute. The metabolic burn is *one consistent factor*,
strikingly conserved per-kg here — evidence *for* the conservation frame, not proof
it is the only cause. The integers below are rounded for an exact witness; the
claim proved is the *structure* (higher rate, shorter life, conserved-within-
tolerance), not the exact biology.

`Nat` model; `decide` on fully-closed concrete literals only.
-/

namespace Gnosis.Body.RateOfLiving

open Gnosis.Body.ConservationOfVitality

/-- Mass-specific burn rate, kcal/kg/day (rounded: men `2500/80`, women `2000/68`). -/
def menRate : Nat := 31
def womenRate : Nat := 29

/-- Lifespan, years (developed-world averages). -/
def menLife : Nat := 76
def womenLife : Nat := 81

/-- Lifetime mass-specific vitality budget = rate × lifespan (the conserved total). -/
def menTotal : Nat := totalVitality menRate menLife
def womenTotal : Nat := totalVitality womenRate womenLife

/-- **Men burn faster** (per kg): the higher rate. -/
theorem men_burn_faster : womenRate < menRate := by decide

/-- **Men die first**: the shorter life — the conservation prediction of a higher
    burn rate. -/
theorem men_die_first : menLife < womenLife := by decide

/-- **The lifetime budget is conserved within tolerance.** The two mass-specific
    lifetime totals differ by at most 10 (here, by 7 of ~2350 — the 0.3% of the
    real figures): the same fixed budget, spent hot-and-short or cool-and-long. -/
theorem lifetime_budget_conserved :
    menTotal - womenTotal ≤ 10 ∧ womenTotal - menTotal ≤ 10 := by decide

/-- **The rate of living** (headline). Men burn faster (higher per-kg rate), die
    first (shorter life), and yet the lifetime mass-specific budget is conserved
    within tolerance: `rate × duration = const`, per kilogram. The conservation
    theory, shown against real rates. -/
theorem the_rate_of_living :
    womenRate < menRate
      ∧ menLife < womenLife
      ∧ menTotal - womenTotal ≤ 10
      ∧ womenTotal - menTotal ≤ 10 := by decide

end Gnosis.Body.RateOfLiving
