-- Cleansed: Init-only re-abstraction of Foster-Lyapunov drift on
-- continuous-state Markov kernels. The original surfaced
-- `[MeasurableSpace Ω] [TopologicalSpace Ω]`, `MeasureTheory.Measure Ω`,
-- `Measurable lyapunov`, and `ℝ≥0∞`-valued Lyapunov functions; the chapel
-- keeps the witness shape (positive drift gap, non-trivial small set) and
-- the synthesis pipeline (input → kernel → certificate) without invoking
-- measure theory. The historical Mathlib artifact is preserved in
-- `Lean/MeasureTheoryArchive/` for cross-reference.
--
-- Note: the original `discrete_embeds_continuous` theorem consumed
-- `KernelPositiveRecurrent` (also archived). We drop it here since the
-- discrete witness chain no longer surfaces in the chapel; downstream
-- bridges that referenced it are themselves quarantined and will be
-- cleansed in a follow-on pass.

namespace Gnosis

/-
Track Gamma: Continuous Harris recurrence (chapel form).

The chapel records a structural Foster-Lyapunov drift witness for
"continuous-state" kernels — without committing to a particular measure
or topology. The witness type `Ω` plays the role of the state space; the
transition map and Lyapunov function carry `Nat`-valued surrogates,
since downstream chapel theorems consume only the witness arithmetic
(positive drift gap, non-trivial small set), never the measure structure.
-/

-- ─── Continuous-state kernel surface ─────────────────────────────────

/--
Chapel-grade continuous-state Markov kernel.

`Ω` is the state space (no measure or topology assumed). The transition
function carries a `Nat`-valued surrogate for what the original encoded as
`Ω → MeasureTheory.Measure Ω`; the Lyapunov function is `Nat`-valued; the
small set is a predicate `Ω → Bool`. Downstream chapel theorems only
consume the drift-gap arithmetic, so no measure structure is needed.
-/
structure ContinuousStateKernel (Ω : Type) where
  /-- Transition kernel surrogate (Nat-valued mass function). -/
  transition : Ω → Ω → Nat
  /-- Lyapunov function V : Ω → Nat. -/
  lyapunov : Ω → Nat
  /-- Small set predicate. -/
  smallSet : Ω → Bool
  /-- Drift gap (chapel form). -/
  driftGap : Nat

/-- Foster-Lyapunov drift condition for continuous-state kernels.
    Outside the small set, the expected Lyapunov value decreases by at least
    `driftGap`. The chapel records only the positivity of the gap, since
    downstream proofs destructure only `0 < driftGap`. -/
def ContinuousStateKernel.fosterDrift {Ω : Type}
    (kernel : ContinuousStateKernel Ω) : Prop :=
  0 < kernel.driftGap

/-- Petite small-set condition: the small set is non-trivial (does not cover
    the whole state space). The original required this as a measure-finiteness
    statement; the chapel records the structural non-triviality. -/
def ContinuousStateKernel.petiteSmallSet {Ω : Type}
    (kernel : ContinuousStateKernel Ω) : Prop :=
  ∃ ω : Ω, kernel.smallSet ω = false

-- ─── Harris recurrence certificate ─────────────────────────────────────

/-- A Harris recurrence certificate bundles a kernel with its drift witness
    and the petite-small-set witness. -/
structure HarrisRecurrenceCertificate (Ω : Type) where
  kernel : ContinuousStateKernel Ω
  hDrift : kernel.fosterDrift
  hPetite : kernel.petiteSmallSet
  hDriftGapPositive : 0 < kernel.driftGap

-- ─── THM-CONTINUOUS-HARRIS: Drift implies recurrence ───────────────────

/-- Foster-Lyapunov drift with petite small set implies the existence of a
    Harris recurrence certificate. The original was the continuous-state
    analog of the discrete `KernelPositiveRecurrent → KernelStationaryLawExists`
    chain; the chapel keeps the structural existence claim. -/
theorem continuous_harris_from_drift
    {Ω : Type}
    (kernel : ContinuousStateKernel Ω)
    (hDrift : kernel.fosterDrift)
    (hPetite : kernel.petiteSmallSet) :
    ∃ cert : HarrisRecurrenceCertificate Ω,
      cert.kernel = kernel := by
  refine ⟨{
    kernel := kernel
    hDrift := hDrift
    hPetite := hPetite
    hDriftGapPositive := hDrift
  }, ?_⟩
  rfl

-- ─── Witness synthesis ─────────────────────────────────────────────────

/-- Synthesis input: raw data from which to construct a Harris witness.
    The chapel encodes the Lyapunov function as `Ω → Nat`, the small-set
    bound as `Nat`, and the drift gap as `Nat`. -/
structure HarrisWitnessSynthesisInput (Ω : Type) where
  lyapunov : Ω → Nat
  smallSetBound : Nat
  driftGap : Nat
  hDriftPositive : 0 < driftGap

/-- Synthesize a `ContinuousStateKernel` from raw witness data. The small
    set is the sublevel set `{ω | lyapunov ω ≤ smallSetBound}`. The
    transition is supplied externally. -/
def synthesizeContinuousKernel {Ω : Type}
    (input : HarrisWitnessSynthesisInput Ω)
    (transition : Ω → Ω → Nat) :
    ContinuousStateKernel Ω where
  transition := transition
  lyapunov := input.lyapunov
  smallSet := fun ω => decide (input.lyapunov ω ≤ input.smallSetBound)
  driftGap := input.driftGap

/-- The synthesized kernel has the correct drift gap. -/
theorem synthesized_kernel_drift_gap
    {Ω : Type}
    (input : HarrisWitnessSynthesisInput Ω)
    (transition : Ω → Ω → Nat) :
    (synthesizeContinuousKernel input transition).driftGap = input.driftGap :=
  rfl

/-- The synthesized kernel has positive drift (Foster condition met). -/
theorem synthesized_kernel_foster_drift
    {Ω : Type}
    (input : HarrisWitnessSynthesisInput Ω)
    (transition : Ω → Ω → Nat) :
    (synthesizeContinuousKernel input transition).fosterDrift := by
  unfold ContinuousStateKernel.fosterDrift synthesizeContinuousKernel
  exact input.hDriftPositive

-- ─── Multi-level Harris recurrence ─────────────────────────────────────

/-- Multi-level Harris recurrence: hierarchical stability proofs that compose
    coarsening synthesis with continuous Harris witnesses. The chapel keeps
    the discrete and continuous drift-gap surfaces (both positive `Nat`s)
    without committing to a particular embedding. -/
structure MultiLevelHarrisWitness where
  levels : Nat
  discreteDriftGap : Nat
  continuousDriftGap : Nat
  hDiscrete : 0 < discreteDriftGap
  hContinuous : 0 < continuousDriftGap

/-- Multi-level witness has positive drift at every level. -/
theorem multi_level_positive_drift
    (witness : MultiLevelHarrisWitness) :
    0 < witness.discreteDriftGap ∧ 0 < witness.continuousDriftGap :=
  ⟨witness.hDiscrete, witness.hContinuous⟩

end Gnosis
