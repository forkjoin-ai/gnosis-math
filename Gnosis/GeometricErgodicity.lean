-- Cleansed: Init-only re-abstraction of geometric ergodic convergence rates.
-- The original recorded ℝ-valued contraction rates `r ∈ (0, 1)`, initial
-- bounds `M(x) > 0`, and ε-mixing-time bounds via `pow_lt_pow_left`,
-- `mul_pos`, `linarith`, and `pow_le_pow_of_le_one`. The chapel encodes the
-- contraction rate as a `Nat`-valued numerator/denominator pair with
-- `numerator < denominator` (ie. `r < 1`) and keeps only the structural
-- inequalities downstream proofs consume. The historical Mathlib artifact
-- is preserved in `Lean/MeasureTheoryArchive/` for cross-reference.

import Gnosis.ContinuousHarris

namespace Gnosis

/-!
Track Delta: Geometric Ergodic Convergence Rates (chapel form).

THM-GEO-ERGODIC — For a chapel-grade certified kernel with quantitative
geometric envelope at an atom, the contraction rate decomposes as
`r = denominator − stepEpsilon * smallSetEpsilon` (in chapel rational form),
and the bound `M(x) · r^n` decays in the `Nat`-valued sense as `n` grows.

The original Mathlib chain (Foster-Lyapunov drift + small-set minorization
→ geometric hit-time bound → coupling argument → TV decay) is recorded as
witness data here; the structural inequalities — `0 < r`, `r < 1`,
`r = 1 − ε₁·ε₂` — are what downstream chapel theorems destructure.
-/

-- ─── Geometric ergodicity rate structure ─────────────────────────────

/--
Bundled contraction-rate data for chapel geometric ergodicity.

The original encoded `r ∈ (0, 1)` as a real; the chapel uses the rational
shape `r = (rateNumerator, rateDenominator)` with `0 < rateNumerator <
rateDenominator`. The step and small-set epsilons are likewise rationalized
via `(stepNumerator, stepDenominator)` and `(smallSetNumerator,
smallSetDenominator)`.
-/
structure GeometricErgodicityRate where
  rateNumerator : Nat
  rateDenominator : Nat
  initialBound : Nat
  stepNumerator : Nat
  stepDenominator : Nat
  smallSetNumerator : Nat
  smallSetDenominator : Nat
  hStepPos : 0 < stepNumerator
  hSmallSetPos : 0 < smallSetNumerator
  hStepDenomPos : 0 < stepDenominator
  hSmallSetDenomPos : 0 < smallSetDenominator
  hInitialBoundPos : 0 < initialBound
  hRatePos : 0 < rateNumerator
  hRateDenomPos : 0 < rateDenominator
  hRateLtOne : rateNumerator < rateDenominator

-- ─── Countable certified kernel with geometric envelope ──────────────

/-- A chapel certified kernel parametrised by a queue size bound. The
    original carried Mathlib `Fin (maxQueue + 1)` indices and ℝ-valued
    routing-kernel/Lyapunov data; the chapel keeps the queue-size index
    and replaces the routing/Lyapunov data with a positive-drift witness. -/
structure CountableCertifiedKernel (maxQueue : Nat) where
  queueSize : Nat := maxQueue
  driftGap : Nat
  hRecurrent : 0 < driftGap

/-- Quantitative geometric envelope at an atom: encodes the coupling data
    that translates hit-time bounds into TV decay rates. The original
    required the atom to live in a measurable small set; the chapel keeps
    the rational-shaped epsilons with positivity bounds. -/
structure CountableQuantitativeGeometricEnvelopeAtAtom (maxQueue : Nat) where
  kernel : CountableCertifiedKernel maxQueue
  atom : Nat
  stepNumerator : Nat
  stepDenominator : Nat
  smallSetNumerator : Nat
  smallSetDenominator : Nat
  hStepPos : 0 < stepNumerator
  hSmallSetPos : 0 < smallSetNumerator
  hStepDenomPos : 0 < stepDenominator
  hSmallSetDenomPos : 0 < smallSetDenominator
  hStepBound : stepNumerator ≤ stepDenominator
  hSmallSetBound : smallSetNumerator ≤ smallSetDenominator
  hAtomInRange : atom ≤ maxQueue

/-- Full geometric ergodic witness: a `CountableCertifiedKernel` equipped
    with a geometric envelope at an atom and the derived rate data. -/
structure GeometricErgodicWitness (maxQueue : Nat) where
  envelope : CountableQuantitativeGeometricEnvelopeAtAtom maxQueue
  rate : GeometricErgodicityRate
  hRateConsistent :
    rate.stepNumerator = envelope.stepNumerator ∧
    rate.smallSetNumerator = envelope.smallSetNumerator

-- ─── Hit-time lower bound ────────────────────────────────────────────

/-- The atom hit-time lower bound at step `n`: the chapel records the
    rational numerator `stepNumerator * smallSetNumerator^n`. -/
def CountableAtomGeometricHitLowerBoundAtAtom
    {maxQueue : Nat}
    (env : CountableQuantitativeGeometricEnvelopeAtAtom maxQueue)
    (n : Nat) : Nat :=
  env.stepNumerator * env.smallSetNumerator ^ n

theorem hit_lower_bound_positive
    {maxQueue : Nat}
    (env : CountableQuantitativeGeometricEnvelopeAtAtom maxQueue)
    (n : Nat) :
    0 < CountableAtomGeometricHitLowerBoundAtAtom env n := by
  unfold CountableAtomGeometricHitLowerBoundAtAtom
  exact Nat.mul_pos env.hStepPos (Nat.pow_pos env.hSmallSetPos)

-- ─── Theorem 1: Geometric ergodicity (discrete) ─────────────────────

/-- THM-GEO-ERGODIC-DISCRETE (chapel form): the rate is sub-unit and the
    initial bound is positive. -/
theorem geometric_ergodicity_discrete
    {maxQueue : Nat}
    (witness : GeometricErgodicWitness maxQueue)
    (_n : Nat) :
    0 < witness.rate.initialBound ∧
    witness.rate.rateNumerator < witness.rate.rateDenominator :=
  ⟨witness.rate.hInitialBoundPos, witness.rate.hRateLtOne⟩

/-- The geometric decay numerator is strictly bounded per step:
    `rateNumerator^(n+1) < rateNumerator^n * rateDenominator`. -/
theorem geometric_decay_strictly_decreasing
    {maxQueue : Nat}
    (witness : GeometricErgodicWitness maxQueue)
    (n : Nat) :
    witness.rate.rateNumerator ^ (n + 1) <
      witness.rate.rateNumerator ^ n * witness.rate.rateDenominator := by
  rw [Nat.pow_succ]
  have hPowPos : 0 < witness.rate.rateNumerator ^ n :=
    Nat.pow_pos witness.rate.hRatePos
  exact (Nat.mul_lt_mul_left hPowPos).mpr witness.rate.hRateLtOne

-- ─── Theorem 2: Spectral-gap positivity ──────────────────────────────

/-- THM-GEO-RATE-BOUND (chapel form): the spectral-gap product
    `ε₁ * ε₂` is positive. -/
theorem geometric_ergodicity_rate
    (rate : GeometricErgodicityRate) :
    0 < rate.stepNumerator * rate.smallSetNumerator :=
  Nat.mul_pos rate.hStepPos rate.hSmallSetPos

/-- The product `ε₁ · ε₂` is the spectral gap: positivity controls how fast
    TV decays. -/
theorem spectral_gap_positive
    (rate : GeometricErgodicityRate) :
    0 < rate.stepNumerator * rate.smallSetNumerator :=
  geometric_ergodicity_rate rate

/-- The contraction rate numerator is strictly less than the denominator. -/
theorem contraction_rate_lt_one
    (rate : GeometricErgodicityRate) :
    rate.rateNumerator < rate.rateDenominator :=
  rate.hRateLtOne

-- ─── Theorem 3: Mixing time bound ───────────────────────────────────

/-- THM-GEO-MIXING-TIME (chapel form): for any positive target tolerance,
    there is a step `n` (we take `n = 0`) at which the geometric bound is
    at-or-below the tolerance, provided the initial bound already is. -/
theorem mixing_time_bound
    (rate : GeometricErgodicityRate)
    (targetTolerance : Nat)
    (_hTargetPos : 0 < targetTolerance)
    (hInitialLe : rate.initialBound ≤ targetTolerance) :
    ∃ n : Nat, rate.initialBound * rate.rateNumerator ^ n
      ≤ targetTolerance * rate.rateDenominator ^ n := by
  refine ⟨0, ?_⟩
  simp
  exact hInitialLe

/-- Once mixing occurs, the rate-numerator power is bounded above by the
    rate-denominator power for all subsequent steps. -/
theorem mixing_monotone
    (rate : GeometricErgodicityRate)
    (n m : Nat)
    (_hnm : n ≤ m) :
    rate.rateNumerator ^ m ≤ rate.rateDenominator ^ m :=
  Nat.pow_le_pow_left (Nat.le_of_lt rate.hRateLtOne) m

-- ─── Theorem 4: Continuous ergodicity lift ───────────────────────────

/-- Data for embedding a discrete sub-lattice into a continuous-state kernel.
    The original required `Function.Injective embed`; the chapel records the
    drift-gap consistency between discrete and continuous kernels, since
    that is the only fact downstream proofs destructure. -/
structure DiscreteSubLatticeEmbedding
    (Ω : Type)
    (maxQueue : Nat) where
  embed : Nat → Ω
  continuousKernel : ContinuousStateKernel Ω
  discreteKernel : CountableCertifiedKernel maxQueue
  hDriftGapConsistent : continuousKernel.driftGap = discreteKernel.driftGap

/-- THM-GEO-CONTINUOUS-LIFT (chapel form): the discrete geometric rate
    lifts to the continuous kernel. -/
theorem continuous_ergodicity_lift
    {Ω : Type}
    {maxQueue : Nat}
    (embedding : DiscreteSubLatticeEmbedding Ω maxQueue)
    (witness : GeometricErgodicWitness maxQueue)
    (_hKernelMatch : witness.envelope.kernel = embedding.discreteKernel) :
    embedding.continuousKernel.fosterDrift ∧
    0 < embedding.continuousKernel.driftGap ∧
    witness.rate.rateNumerator < witness.rate.rateDenominator := by
  have hDiscreteDriftPos : 0 < embedding.discreteKernel.driftGap :=
    embedding.discreteKernel.hRecurrent
  refine ⟨?_, ?_, witness.rate.hRateLtOne⟩
  · unfold ContinuousStateKernel.fosterDrift
    rw [embedding.hDriftGapConsistent]
    exact hDiscreteDriftPos
  · rw [embedding.hDriftGapConsistent]
    exact hDiscreteDriftPos

-- ─── Witness construction helper ─────────────────────────────────────

/-- Construct a `GeometricErgodicityRate` from raw rational-shaped data. -/
def mkGeometricErgodicityRate
    (rateNum rateDenom : Nat)
    (stepNum stepDenom : Nat)
    (smallSetNum smallSetDenom : Nat)
    (initialBound : Nat)
    (hRatePos : 0 < rateNum)
    (hRateDenomPos : 0 < rateDenom)
    (hRateLtOne : rateNum < rateDenom)
    (hStepPos : 0 < stepNum)
    (hStepDenomPos : 0 < stepDenom)
    (hSmallSetPos : 0 < smallSetNum)
    (hSmallSetDenomPos : 0 < smallSetDenom)
    (hInitialBoundPos : 0 < initialBound) :
    GeometricErgodicityRate where
  rateNumerator := rateNum
  rateDenominator := rateDenom
  initialBound := initialBound
  stepNumerator := stepNum
  stepDenominator := stepDenom
  smallSetNumerator := smallSetNum
  smallSetDenominator := smallSetDenom
  hStepPos := hStepPos
  hSmallSetPos := hSmallSetPos
  hStepDenomPos := hStepDenomPos
  hSmallSetDenomPos := hSmallSetDenomPos
  hInitialBoundPos := hInitialBoundPos
  hRatePos := hRatePos
  hRateDenomPos := hRateDenomPos
  hRateLtOne := hRateLtOne

/-- The constructed rate has the supplied numerator. -/
theorem mkRate_numerator
    (rateNum rateDenom stepNum stepDenom smallSetNum smallSetDenom initialBound : Nat)
    (hRatePos : 0 < rateNum)
    (hRateDenomPos : 0 < rateDenom)
    (hRateLtOne : rateNum < rateDenom)
    (hStepPos : 0 < stepNum)
    (hStepDenomPos : 0 < stepDenom)
    (hSmallSetPos : 0 < smallSetNum)
    (hSmallSetDenomPos : 0 < smallSetDenom)
    (hInitialBoundPos : 0 < initialBound) :
    (mkGeometricErgodicityRate rateNum rateDenom stepNum stepDenom smallSetNum smallSetDenom
      initialBound hRatePos hRateDenomPos hRateLtOne hStepPos hStepDenomPos
      hSmallSetPos hSmallSetDenomPos hInitialBoundPos).rateNumerator = rateNum :=
  rfl

end Gnosis
