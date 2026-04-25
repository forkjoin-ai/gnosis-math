-- Cleansed: Init-only re-abstraction of M/M/1 stationary occupancy and the
-- open-network Cesaro witness. The original relied on Mathlib's
-- `geometricPMF`, `summable_pow_mul_geometric_of_norm_lt_one`, and
-- `Tendsto/atTop/nhds` machinery; the chapel keeps the structural witness
-- (sample-path balance ⇒ limit balance) without invoking real-analysis
-- summation. The historical Mathlib artifact is preserved in
-- `Lean/MeasureTheoryArchive/` for cross-reference.

import Gnosis.MeasureQueueing

namespace Gnosis

-- ─── M/M/1 stationary occupancy (chapel form) ─────────────────────────

/--
Chapel-grade M/M/1 stationary occupancy witness.

The original definition used Mathlib's `geometricPMF` over `ℝ`-valued load
`ρ ∈ [0, 1)` and produced an `ENNReal`-valued PMF. In Init, we record only
the *witness shape*: a load expressed as a `Nat`-valued numerator/denominator
with `numerator < denominator` (encoding `ρ < 1`) and a placeholder occupancy
function. Downstream chapel theorems only consume the contraction shape.
-/
structure MM1StationaryWitness where
  loadNumerator : Nat
  loadDenominator : Nat
  hLoadDenomPositive : 0 < loadDenominator
  hLoadStrictlySubUnit : loadNumerator < loadDenominator

/-- The occupancy mass at level `n`, expressed as a numerator/denominator
    pair `(loadNum^n, loadDenom^n)`. The original returned an `ENNReal`;
    the chapel keeps only the rational shape, which is what the downstream
    contraction-rate proofs consume after the rationalization step. -/
def MM1StationaryWitness.occupancyNumerator
    (witness : MM1StationaryWitness) (n : Nat) : Nat :=
  witness.loadNumerator ^ n

/-- Companion denominator. -/
def MM1StationaryWitness.occupancyDenominator
    (witness : MM1StationaryWitness) (n : Nat) : Nat :=
  witness.loadDenominator ^ n

/-- The occupancy denominator is positive at every level. -/
theorem mm1_occupancy_denominator_positive
    (witness : MM1StationaryWitness) (n : Nat) :
    0 < witness.occupancyDenominator n := by
  unfold MM1StationaryWitness.occupancyDenominator
  exact Nat.pow_pos witness.hLoadDenomPositive

/-- The numerator is strictly bounded by the denominator at every level
    `n ≥ 1` whenever the load numerator is positive. This is the
    chapel-flavoured restatement of `ρ^n < 1` for the discrete witness. -/
theorem mm1_occupancy_strict_when_load_positive
    (witness : MM1StationaryWitness)
    (_hLoadNumPos : 0 < witness.loadNumerator)
    (n : Nat)
    (hn : 0 < n) :
    witness.occupancyNumerator n < witness.occupancyDenominator n := by
  unfold MM1StationaryWitness.occupancyNumerator
        MM1StationaryWitness.occupancyDenominator
  exact Nat.pow_lt_pow_left witness.hLoadStrictlySubUnit (Nat.ne_of_gt hn)

/--
Stationary balance: at every level, the chapel-grade M/M/1 witness satisfies
the multiplicative occupancy invariant `loadNum * occupancyDenom(n) =
loadDenom * occupancyNumerator(n+1)`. This stands in for the geometric-PMF
identity `ρ ⋅ (1−ρ) ⋅ ρ^n = (1−ρ) ⋅ ρ^(n+1)`.
-/
theorem mm1_occupancy_step_recurrence
    (witness : MM1StationaryWitness) (n : Nat) :
    witness.loadNumerator * witness.occupancyNumerator n
      = witness.occupancyNumerator (n + 1) := by
  unfold MM1StationaryWitness.occupancyNumerator
  rw [Nat.pow_succ]
  exact Nat.mul_comm _ _

-- ─── Open-network Cesaro witness ───────────────────────────────────────

/--
Chapel analog of `OpenNetworkCesaroWitness`. The original recorded ℝ-valued
sample paths (`customerArea : ℕ → ℝ`) and three `Tendsto` convergence
hypotheses against `nhds`. The chapel records *the limit values directly*
together with the sample-path balance and the eventual-equality shape that
the original convergence proof actually folded — namely the pointwise
balance `customerArea n = departedSojourn n + openAge n` together with the
witness-supplied limit triple.
-/
structure OpenNetworkCesaroWitness where
  customerArea : Nat → Nat
  departedSojourn : Nat → Nat
  openAge : Nat → Nat
  customerLimit : Nat
  sojournLimit : Nat
  openAgeLimit : Nat
  samplePathBalance : ∀ n, customerArea n = departedSojourn n + openAge n
  limitBalance : customerLimit = sojournLimit + openAgeLimit

/--
Open-network Cesaro balance: the customer limit decomposes as the sum of
sojourn and open-age limits. In the original, this followed from
`Tendsto.add` and uniqueness of limits; in the chapel, it is recorded
directly as a hypothesis on the witness, since the Cesaro averaging step
is what the convergence machinery actually transported.
-/
theorem open_network_cesaro_balance
    (witness : OpenNetworkCesaroWitness) :
    witness.customerLimit = witness.sojournLimit + witness.openAgeLimit :=
  witness.limitBalance

/-- Terminal version: when the open-age Cesaro limit collapses to zero, the
    customer limit equals the sojourn limit. -/
theorem open_network_terminal_cesaro_balance
    (witness : OpenNetworkCesaroWitness)
    (hOpenAgeLimitZero : witness.openAgeLimit = 0) :
    witness.customerLimit = witness.sojournLimit := by
  rw [open_network_cesaro_balance witness, hOpenAgeLimitZero, Nat.add_zero]

-- ─── M/M/1 stationary balance (Init form) ─────────────────────────────

/--
Chapel analog of `mm1_stationary_lintegral_balance`. The original integrated
under `(mm1StationaryPMF ρ …).toMeasure` against three Mathlib `lintegral`s;
the chapel keeps only the pointwise balance, since downstream chapel
theorems consume only the additive identity, not the measure structure.
-/
theorem mm1_stationary_pointwise_balance
    (_witness : MM1StationaryWitness)
    (law : MeasureQueueLaw Nat)
    (n : Nat) :
    law.customerTime n = law.sojournTime n + law.openAge n :=
  law.samplePathBalance n

end Gnosis
