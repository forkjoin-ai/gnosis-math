-- Cleansed: Init-only re-abstraction of weighted-queue series. The original
-- relied on Mathlib MeasureTheory (ℝ≥0∞ mass and lintegral) — see
-- `Lean/MeasureTheoryArchive/` for the historical Mathlib-grade artifact.
-- The structural content (sample-path balance and Little-Law-shaped equalities)
-- survives in `Nat`-indexed form, since the chapel theorems that consume this
-- file only ever exploit the additive shape, never the measure structure.

namespace BuleyeanMath

-- ─── Nat-valued weighted queue series ─────────────────────────────────

/--
Chapel-grade weighted queue series.

Each sample path carries a customer time, a sojourn time, and an open-age
residual. The sample-path balance `customerTime ω = sojournTime ω + openAge ω`
is the only structural invariant the downstream chapel theorems consume; the
original Mathlib version expressed mass in `ℝ≥0∞` and integrated against
`Measure`, but the chapel proofs only ever folded the balance equality.
-/
structure WeightedQueueSeries (Ω : Type) where
  mass : Ω → Nat
  customerTime : Ω → Nat
  sojournTime : Ω → Nat
  openAge : Ω → Nat
  samplePathBalance : ∀ ω, customerTime ω = sojournTime ω + openAge ω

/-- Pointwise weighted-customer mass at a sample point. -/
def WeightedQueueSeries.weightedCustomerAt
    {Ω : Type} (series : WeightedQueueSeries Ω) (ω : Ω) : Nat :=
  series.mass ω * series.customerTime ω

/-- Pointwise weighted-sojourn mass at a sample point. -/
def WeightedQueueSeries.weightedSojournAt
    {Ω : Type} (series : WeightedQueueSeries Ω) (ω : Ω) : Nat :=
  series.mass ω * series.sojournTime ω

/-- Pointwise weighted-open-age mass at a sample point. -/
def WeightedQueueSeries.weightedOpenAgeAt
    {Ω : Type} (series : WeightedQueueSeries Ω) (ω : Ω) : Nat :=
  series.mass ω * series.openAge ω

/--
Pointwise sample-path balance under an arbitrary mass weighting.

This is the structural content of the original `weighted_queue_tsum_balance`
theorem: at every sample point, weighted customer time equals weighted sojourn
plus weighted open-age. The Mathlib version aggregated under `tsum`; the
chapel keeps only the pointwise statement, which is what downstream proofs
actually destructure.
-/
theorem weighted_queue_pointwise_balance
    {Ω : Type}
    (series : WeightedQueueSeries Ω)
    (ω : Ω) :
    series.weightedCustomerAt ω
      = series.weightedSojournAt ω + series.weightedOpenAgeAt ω := by
  unfold WeightedQueueSeries.weightedCustomerAt
        WeightedQueueSeries.weightedSojournAt
        WeightedQueueSeries.weightedOpenAgeAt
  rw [series.samplePathBalance ω, Nat.mul_add]

/-- Terminal version: when open-age is zero pointwise, weighted-customer mass
    collapses to weighted-sojourn mass. -/
theorem weighted_queue_pointwise_terminal_balance
    {Ω : Type}
    (series : WeightedQueueSeries Ω)
    (hOpenAgeZero : ∀ ω, series.openAge ω = 0)
    (ω : Ω) :
    series.weightedCustomerAt ω = series.weightedSojournAt ω := by
  have hStep := weighted_queue_pointwise_balance series ω
  unfold WeightedQueueSeries.weightedOpenAgeAt at hStep
  rw [hOpenAgeZero ω, Nat.mul_zero, Nat.add_zero] at hStep
  exact hStep

-- ─── PMF-shaped balance (Nat-valued) ─────────────────────────────────

/--
Discrete chapel analog of the original PMF-weighted balance lemma.

Given a `Nat`-valued mass function `p : Ω → Nat` and three `Nat`-valued
quantities satisfying the sample-path balance, the pointwise weighting
preserves the additive decomposition. The Mathlib version summed under
`tsum`; the chapel records the structural identity at the sample-point level.
-/
theorem pmf_queue_pointwise_balance
    {Ω : Type}
    (p : Ω → Nat)
    {customerTime sojournTime openAge : Ω → Nat}
    (hBalance : ∀ ω, customerTime ω = sojournTime ω + openAge ω)
    (ω : Ω) :
    p ω * customerTime ω
      = p ω * sojournTime ω + p ω * openAge ω := by
  rw [hBalance ω, Nat.mul_add]

/-- Terminal version of the PMF balance. -/
theorem pmf_queue_pointwise_terminal_balance
    {Ω : Type}
    (p : Ω → Nat)
    {customerTime sojournTime openAge : Ω → Nat}
    (hBalance : ∀ ω, customerTime ω = sojournTime ω + openAge ω)
    (hOpenAgeZero : ∀ ω, openAge ω = 0)
    (ω : Ω) :
    p ω * customerTime ω = p ω * sojournTime ω := by
  have hStep := pmf_queue_pointwise_balance p hBalance ω
  rw [hOpenAgeZero ω, Nat.mul_zero, Nat.add_zero] at hStep
  exact hStep

-- ─── Measure-shaped surface (chapel-flavoured) ────────────────────────

/--
Chapel analog of `MeasureQueueLaw`. The Mathlib version carried
`Measurable` predicates against a `MeasurableSpace` instance; the chapel
keeps only the sample-path balance, which is the sole property destructured
by downstream proofs.
-/
structure MeasureQueueLaw (Ω : Type) where
  customerTime : Ω → Nat
  sojournTime : Ω → Nat
  openAge : Ω → Nat
  samplePathBalance : ∀ ω, customerTime ω = sojournTime ω + openAge ω

/--
Pointwise version of `measure_queue_lintegral_balance`. The original integrated
against an arbitrary measure `μ`; the chapel records the equality at every
sample point, which is the only step the original proof actually invoked
(`lintegral_congr_ae` then `lintegral_add_left`).
-/
theorem measure_queue_pointwise_balance
    {Ω : Type}
    (law : MeasureQueueLaw Ω)
    (ω : Ω) :
    law.customerTime ω = law.sojournTime ω + law.openAge ω :=
  law.samplePathBalance ω

/-- Terminal version: when the open-age component is uniformly zero, the
    customer-time equals the sojourn-time pointwise. -/
theorem measure_queue_pointwise_terminal_balance
    {Ω : Type}
    (law : MeasureQueueLaw Ω)
    (hOpenAgeZero : ∀ ω, law.openAge ω = 0)
    (ω : Ω) :
    law.customerTime ω = law.sojournTime ω := by
  rw [law.samplePathBalance ω, hOpenAgeZero ω, Nat.add_zero]

/-- PMF analog: same statement, named so downstream chapel proofs that
    formerly invoked the PMF-specific lemma can switch with a single rename. -/
theorem pmf_queue_pointwise_law_balance
    {Ω : Type}
    (_p : Ω → Nat)
    (law : MeasureQueueLaw Ω)
    (ω : Ω) :
    law.customerTime ω = law.sojournTime ω + law.openAge ω :=
  law.samplePathBalance ω

/-- Terminal PMF analog. -/
theorem pmf_queue_pointwise_law_terminal_balance
    {Ω : Type}
    (_p : Ω → Nat)
    (law : MeasureQueueLaw Ω)
    (hOpenAgeZero : ∀ ω, law.openAge ω = 0)
    (ω : Ω) :
    law.customerTime ω = law.sojournTime ω :=
  measure_queue_pointwise_terminal_balance law hOpenAgeZero ω

-- ─── Truncation family ────────────────────────────────────────────────

/--
Chapel analog of `MeasureQueueTruncationFamily`. The original recorded
`Measurable` predicates per truncation level; the chapel keeps the
monotonicity in `Nat → Ω → Nat` form and the sample-path balance at every
level. Downstream proofs only consume the monotone-supremum shape.
-/
structure MeasureQueueTruncationFamily (Ω : Type) where
  customerTime : Nat → Ω → Nat
  sojournTime : Nat → Ω → Nat
  openAge : Nat → Ω → Nat
  monotoneCustomerTime : ∀ {i j : Nat}, i ≤ j → ∀ ω, customerTime i ω ≤ customerTime j ω
  monotoneSojournTime : ∀ {i j : Nat}, i ≤ j → ∀ ω, sojournTime i ω ≤ sojournTime j ω
  monotoneOpenAge : ∀ {i j : Nat}, i ≤ j → ∀ ω, openAge i ω ≤ openAge j ω
  samplePathBalance : ∀ n ω, customerTime n ω = sojournTime n ω + openAge n ω

/-- Pointwise sample-path balance at every truncation level. The Mathlib
    version converted the pointwise balance to an integral identity by
    monotone convergence; the chapel uses the pointwise form directly. -/
theorem measure_queue_truncation_pointwise_balance
    {Ω : Type}
    (family : MeasureQueueTruncationFamily Ω)
    (n : Nat) (ω : Ω) :
    family.customerTime n ω = family.sojournTime n ω + family.openAge n ω :=
  family.samplePathBalance n ω

/-- Terminal version of the truncation balance. -/
theorem measure_queue_truncation_pointwise_terminal_balance
    {Ω : Type}
    (family : MeasureQueueTruncationFamily Ω)
    (hOpenAgeZero : ∀ n ω, family.openAge n ω = 0)
    (n : Nat) (ω : Ω) :
    family.customerTime n ω = family.sojournTime n ω := by
  rw [family.samplePathBalance n ω, hOpenAgeZero n ω, Nat.add_zero]

end BuleyeanMath
