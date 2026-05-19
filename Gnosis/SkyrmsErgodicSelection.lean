import Gnosis.SkyrmsUltraLongRunEquilibrium

/-
  SkyrmsErgodicSelection.lean
  ===========================

  Discrete stochastic-stability witness for the *unconditional* reading
  of `Gnosis.SkyrmsUltraLongRunEquilibrium`.

  ## What this module provides

  Where `SkyrmsUltraLongRunEquilibrium` builds a deterministic finite
  mutation path from the Nash polarization trap to the Skyrms
  ultra-long-run (ULR) fixed point, this module lifts the picture to a
  `Nat`-weighted mutation kernel on lumped basins (`nash` / `mid` /
  `ulr`) and shows:

  1. The kernel is **irreducible** — every basin reaches every basin
     in one step with strictly positive `Nat` weight.
  2. The kernel is **ULR-attractive** — every basin has positive
     transition weight into the ULR basin (the hypothesis the user
     asked us to formalize).
  3. The kernel is **Nash-leaky per row** — every row places strictly
     more total mass on non-Nash destinations (`.mid + .ulr`) than on
     the Nash self-loop. This is the discrete drift-away-from-Nash
     condition that underwrites long-run Nash-mass decay (and is the
     honestly statable form of "ULR-biased": the Nash row keeps a
     non-trivial self-loop, but its *escape* mass strictly exceeds it).
  4. Starting from *every* basin (Nash Dirac, mid Dirac, ULR Dirac, or
     the uniform start), the mass at the ULR basin strictly exceeds
     the mass at the Nash basin after a small finite number of
     pushforward steps, and the dominance only widens at later steps
     we check.
  5. The lumped basins inherit the per-player Pareto witnesses from
     `SkyrmsUltraLongRunEquilibrium` (`ulr_strictly_dominates_nash_per_player`
     and `ulr_strictly_dominates_nash_jointly`), so mass dominance
     and payoff dominance hold *simultaneously* on the same state
     space.

  Combined, these pieces deliver the discrete-combinatorial form of
  the "near-certain" unconditional claim: for the kernel class we can
  express in Init Lean, ULR strictly dominates Nash in finite-time
  mass *and* in per-player payoff, from any starting basin.

  ## Honesty boundary

  We do **not** prove the genuine measure-theoretic ergodic-stationary
  theorem ("for every irreducible kernel with positive ULR-bias, the
  long-run occupation measure of ULR strictly exceeds that of the Nash
  trap"). That theorem requires real-analytic limits, Markov-chain
  convergence theorems, and Perron-Frobenius spectral arguments which
  are not available in Init-only Lean. What we *do* prove is the
  discrete finite-time witness on a concrete biased-toward-ULR kernel,
  with the structural predicates (`Irreducible`, `UlrAttractive`,
     `NashLeaky`) made explicit so the bridge to a future Mathlib upgrade
  is well-typed: those exact predicates are the natural hypotheses of
  the limit theorem, and the names line up.

  This module is *not* `Gnosis.ErgodicConvergence`'s long-promised
  kernel infrastructure (that file is currently a sequence-equality
  stub: `isStructurallyIntegrated ops := ops = invariantBasis`). The
  kernel infrastructure is provided here, self-contained.

  Imports `Gnosis.SkyrmsUltraLongRunEquilibrium` only. Zero `sorry`,
  zero new `axiom`.
-/


namespace SkyrmsErgodicSelection

open SkyrmsUltraLongRunEquilibrium
open Gnosis.SkyrmsBuleyEquilibria (Dominates)

/-! ## Lumped basins -/

/-- The three lumped basins of the Skyrms ULR picture: the Nash
    polarization trap, the mid corridor, and the ULR fixed point. -/
inductive Basin where
  | nash | mid | ulr
  deriving DecidableEq, Repr

/-! ## Row distributions and kernels -/

/-- A per-state Nat-weighted row: how mass leaving a basin in one step
    is split across destination basins. -/
structure Row where
  toNash : Nat
  toMid  : Nat
  toUlr  : Nat
  deriving DecidableEq, Repr

/-- Total outflow of a row. -/
def Row.total (r : Row) : Nat := r.toNash + r.toMid + r.toUlr

/-- Common denominator: each row is required to sum to `kernelDenom`.
    With `kernelDenom = 100`, individual row entries read as percent
    weights without any `Nat` truncation. -/
def kernelDenom : Nat := 100

/-- A mutation kernel on `Basin`: three rows, one per source basin. -/
structure MutationKernel where
  fromNash : Row
  fromMid  : Row
  fromUlr  : Row
  deriving Repr

/-- Look up the row indexed by source basin. -/
def MutationKernel.rowFrom (k : MutationKernel) (b : Basin) : Row :=
  match b with
  | .nash => k.fromNash
  | .mid  => k.fromMid
  | .ulr  => k.fromUlr

/-- Look up a single transition weight `w(b, b')`. -/
def MutationKernel.weight (k : MutationKernel) (b b' : Basin) : Nat :=
  let r := k.rowFrom b
  match b' with
  | .nash => r.toNash
  | .mid  => r.toMid
  | .ulr  => r.toUlr

/-- Kernel well-formedness: every row sums to `kernelDenom`. -/
def MutationKernel.WellFormed (k : MutationKernel) : Prop :=
  k.fromNash.total = kernelDenom ∧
  k.fromMid.total  = kernelDenom ∧
  k.fromUlr.total  = kernelDenom

/-! ## Structural predicates

These three predicates are the discrete analogues of the standard
stochastic-stability hypotheses. They are stated at the `Nat`-weight
level so a downstream Mathlib lift can quote them verbatim. -/

/-- Irreducibility: every transition has strictly positive `Nat`
    weight. (One-step coverage; the strongest discrete reading.) -/
def MutationKernel.Irreducible (k : MutationKernel) : Prop :=
  ∀ b b' : Basin, 0 < k.weight b b'

/-- ULR-attractiveness: every basin has positive weight into the ULR
    basin. This is the "positive transition probabilities into the
    ULR basin" hypothesis spelled out in `Nat`. -/
def MutationKernel.UlrAttractive (k : MutationKernel) : Prop :=
  ∀ b : Basin, 0 < k.weight b .ulr

/-- Nash-leaky per row: every row places strictly more mass on
    non-Nash destinations (`.mid + .ulr`) than on the Nash
    self-loop. This is the discrete drift-away-from-Nash condition
    that underwrites long-run Nash-mass decay. It is strictly weaker
    than the naive "every row puts more on `.ulr` than on `.nash`":
    the Nash basin is allowed to keep a non-trivial self-loop, as
    long as the *escape* mass exceeds it. -/
def MutationKernel.NashLeaky (k : MutationKernel) : Prop :=
  ∀ b : Basin, k.weight b .nash < k.weight b .mid + k.weight b .ulr

/-! ## Concrete biased-toward-ULR kernel

  From Nash : stay 30, advance to mid 50, jump to ULR 20.
  From mid  : revert 10, stay 30, advance to ULR 60.
  From ULR  : revert 5,  regress 5, stay 90.

The kernel mirrors the deterministic six-step path of
`SkyrmsUltraLongRunEquilibrium.iterate` while adding a small uniform
mutation that keeps every transition strictly positive — so every
hypothesis (irreducibility, ULR-attractive, ULR-biased) holds
non-trivially. -/

def biasedKernel : MutationKernel where
  fromNash := { toNash := 30, toMid := 50, toUlr := 20 }
  fromMid  := { toNash := 10, toMid := 30, toUlr := 60 }
  fromUlr  := { toNash := 5,  toMid := 5,  toUlr := 90 }

theorem biased_kernel_well_formed : biasedKernel.WellFormed := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

theorem biased_kernel_irreducible : biasedKernel.Irreducible := by
  intro b b'
  cases b <;> cases b' <;> decide

theorem biased_kernel_ulr_attractive : biasedKernel.UlrAttractive := by
  intro b
  cases b <;> decide

theorem biased_kernel_nash_leaky : biasedKernel.NashLeaky := by
  intro b
  cases b <;> decide

/-! ## Mass distributions and exact pushforward -/

/-- A `Nat`-valued mass distribution over basins. -/
structure Dist where
  massNash : Nat
  massMid  : Nat
  massUlr  : Nat
  deriving DecidableEq, Repr

/-- Total mass of a distribution. -/
def Dist.total (d : Dist) : Nat := d.massNash + d.massMid + d.massUlr

/-- One-step pushforward.

    Each basin's new mass is a weighted sum of incoming flows. We do
    *not* divide out the kernel denominator, so each step multiplies
    the total mass by `kernelDenom = 100`. This keeps every
    pushforward computation exact in `Nat`, with no truncation. -/
def step (k : MutationKernel) (d : Dist) : Dist where
  massNash :=
    d.massNash * k.weight .nash .nash +
    d.massMid  * k.weight .mid  .nash +
    d.massUlr  * k.weight .ulr  .nash
  massMid :=
    d.massNash * k.weight .nash .mid +
    d.massMid  * k.weight .mid  .mid +
    d.massUlr  * k.weight .ulr  .mid
  massUlr :=
    d.massNash * k.weight .nash .ulr +
    d.massMid  * k.weight .mid  .ulr +
    d.massUlr  * k.weight .ulr  .ulr

/-- Iterated pushforward. -/
def pushforward (k : MutationKernel) : Nat → Dist → Dist
  | 0,     d => d
  | n + 1, d => step k (pushforward k n d)

/-! ## Starting distributions

Four canonical starting points: a Dirac on each basin (worst-case
single-state initial conditions) plus a uniform start (the symmetric
ignorance prior). Mass-domination from *all four* is the discrete
analogue of "the long-run occupation favors ULR regardless of where
the chain begins." -/

def fromNashDirac : Dist := { massNash := 1, massMid := 0, massUlr := 0 }
def fromMidDirac  : Dist := { massNash := 0, massMid := 1, massUlr := 0 }
def fromUlrDirac  : Dist := { massNash := 0, massMid := 0, massUlr := 1 }
def fromUniform   : Dist := { massNash := 1, massMid := 1, massUlr := 1 }

/-! ## Finite-time ULR-dominates-Nash mass witnesses -/

/-- One step from the mid Dirac already lands more mass on ULR (60)
    than on Nash (10). -/
theorem from_mid_ulr_dominates_nash_after_one_step :
    (pushforward biasedKernel 1 fromMidDirac).massUlr >
      (pushforward biasedKernel 1 fromMidDirac).massNash := by
  native_decide

/-- One step from the ULR Dirac retains 90% on ULR vs 5% on Nash. -/
theorem from_ulr_ulr_dominates_nash_after_one_step :
    (pushforward biasedKernel 1 fromUlrDirac).massUlr >
      (pushforward biasedKernel 1 fromUlrDirac).massNash := by
  native_decide

/-- One step from the uniform start: ULR mass 170, Nash mass 45. -/
theorem from_uniform_ulr_dominates_nash_after_one_step :
    (pushforward biasedKernel 1 fromUniform).massUlr >
      (pushforward biasedKernel 1 fromUniform).massNash := by
  native_decide

/-- The Nash basin is the worst-case starting point. After **one**
    step from the Nash Dirac, ULR mass (20) is still less than Nash
    mass (30) — there is genuine drag from the Nash self-loop. -/
theorem from_nash_ulr_does_not_dominate_at_step_one :
    (pushforward biasedKernel 1 fromNashDirac).massUlr <
      (pushforward biasedKernel 1 fromNashDirac).massNash := by
  native_decide

/-- After **two** steps from the Nash Dirac, the drift overcomes the
    Nash self-loop: ULR mass (5400) strictly exceeds Nash mass (1500). -/
theorem from_nash_ulr_dominates_nash_after_two_steps :
    (pushforward biasedKernel 2 fromNashDirac).massUlr >
      (pushforward biasedKernel 2 fromNashDirac).massNash := by
  native_decide

/-- After **three** steps from the Nash Dirac, ULR mass exceeds Nash
    mass by more than a factor of six (702000 / 103000 ≈ 6.81). -/
theorem from_nash_ulr_dominates_nash_after_three_steps :
    (pushforward biasedKernel 3 fromNashDirac).massUlr >
      (pushforward biasedKernel 3 fromNashDirac).massNash := by
  native_decide

theorem from_nash_ulr_mass_at_least_six_times_nash_at_step_three :
    (pushforward biasedKernel 3 fromNashDirac).massUlr ≥
      6 * (pushforward biasedKernel 3 fromNashDirac).massNash := by
  native_decide

/-- After **five** steps from the Nash Dirac, ULR mass exceeds Nash
    mass by more than a factor of nine. The drift is monotone in the
    steps we have checked. -/
theorem from_nash_ulr_dominates_nash_after_five_steps :
    (pushforward biasedKernel 5 fromNashDirac).massUlr >
      (pushforward biasedKernel 5 fromNashDirac).massNash := by
  native_decide

theorem from_nash_ulr_mass_at_least_nine_times_nash_at_step_five :
    (pushforward biasedKernel 5 fromNashDirac).massUlr ≥
      9 * (pushforward biasedKernel 5 fromNashDirac).massNash := by
  native_decide

/-! ## Mass conservation -/

/-- Mass conservation: each step multiplies total mass by `kernelDenom`,
    so after three steps from a unit-mass Nash Dirac the total is
    `100 ^ 3 = 10 ^ 6`. This is the exact-`Nat` form of "the
    pushforward preserves probability mass." -/
theorem from_nash_total_mass_after_three_steps :
    (pushforward biasedKernel 3 fromNashDirac).total = 100 ^ 3 := by
  native_decide

/-- Same conservation, five steps. Total mass = `100 ^ 5 = 10 ^ 10`. -/
theorem from_nash_total_mass_after_five_steps :
    (pushforward biasedKernel 5 fromNashDirac).total = 100 ^ 5 := by
  native_decide

/-! ## Bridge to `PolarizationState` and the Pareto witnesses

The lumped basins refer to concrete `PolarizationState` values from
`SkyrmsUltraLongRunEquilibrium`:

* `nash` ↔ `nashPolarizationTrap`,
* `mid`  ↔ `iterate 3 nashPolarizationTrap` (the deterministic-path
  midpoint),
* `ulr`  ↔ `skyrmsUltraLongRunFixedPoint`.

This bridge lets the existing per-player and joint Pareto theorems
read out as basin-level dominance results. -/

def basinPolarizationState : Basin → PolarizationState
  | .nash => nashPolarizationTrap
  | .mid  => SkyrmsUltraLongRunEquilibrium.iterate 3 nashPolarizationTrap
  | .ulr  => skyrmsUltraLongRunFixedPoint

theorem nash_basin_is_nash_polarization_trap :
    basinPolarizationState .nash = nashPolarizationTrap := rfl

theorem ulr_basin_is_skyrms_ulr_fixed_point :
    basinPolarizationState .ulr = skyrmsUltraLongRunFixedPoint := rfl

/-- Per-player Pareto witness reread on the lumped basins. -/
theorem ulr_basin_strictly_dominates_nash_per_player :
    Dominates (payoffAOf (basinPolarizationState .ulr))
      (payoffAOf (basinPolarizationState .nash)) ∧
    Dominates (payoffBOf (basinPolarizationState .ulr))
      (payoffBOf (basinPolarizationState .nash)) := by
  unfold basinPolarizationState
  exact ulr_strictly_dominates_nash_per_player

/-- Joint Pareto witness reread on the lumped basins. -/
theorem ulr_basin_strictly_dominates_nash_jointly :
    Dominates (jointWelfare (basinPolarizationState .ulr))
      (jointWelfare (basinPolarizationState .nash)) := by
  unfold basinPolarizationState
  exact ulr_strictly_dominates_nash_jointly

/-! ## The discrete unconditional witness

This is the package theorem: in a single statement we record (a) the
structural predicates the user asked us to formalize, (b) a finite-
time ULR-mass-dominates-Nash-mass witness from *every* starting basin,
and (c) the per-player and joint Pareto dominance carried over from
`SkyrmsUltraLongRunEquilibrium`. -/

theorem ulr_dominates_nash_unconditional_discrete :
    biasedKernel.WellFormed ∧
    biasedKernel.Irreducible ∧
    biasedKernel.UlrAttractive ∧
    biasedKernel.NashLeaky ∧
    (pushforward biasedKernel 2 fromNashDirac).massUlr >
      (pushforward biasedKernel 2 fromNashDirac).massNash ∧
    (pushforward biasedKernel 1 fromMidDirac).massUlr >
      (pushforward biasedKernel 1 fromMidDirac).massNash ∧
    (pushforward biasedKernel 1 fromUlrDirac).massUlr >
      (pushforward biasedKernel 1 fromUlrDirac).massNash ∧
    (pushforward biasedKernel 1 fromUniform).massUlr >
      (pushforward biasedKernel 1 fromUniform).massNash ∧
    Dominates (payoffAOf (basinPolarizationState .ulr))
      (payoffAOf (basinPolarizationState .nash)) ∧
    Dominates (payoffBOf (basinPolarizationState .ulr))
      (payoffBOf (basinPolarizationState .nash)) ∧
    Dominates (jointWelfare (basinPolarizationState .ulr))
      (jointWelfare (basinPolarizationState .nash)) := by
  refine ⟨biased_kernel_well_formed,
          biased_kernel_irreducible,
          biased_kernel_ulr_attractive,
          biased_kernel_nash_leaky,
          from_nash_ulr_dominates_nash_after_two_steps,
          from_mid_ulr_dominates_nash_after_one_step,
          from_ulr_ulr_dominates_nash_after_one_step,
          from_uniform_ulr_dominates_nash_after_one_step,
          ?_, ?_, ?_⟩
  · exact ulr_basin_strictly_dominates_nash_per_player.1
  · exact ulr_basin_strictly_dominates_nash_per_player.2
  · exact ulr_basin_strictly_dominates_nash_jointly

/-! ## Honesty note

`ulr_dominates_nash_unconditional_discrete` is the most honest
unconditional statement available in Init-only Lean. It says:

  • There exists a concrete kernel — `biasedKernel` — that is
    well-formed, irreducible, ULR-attractive, and Nash-leaky per row.
  • Under that kernel, ULR mass strictly dominates Nash mass after
    one or two steps from every starting Dirac and from the uniform
    start; the dominance widens to a ≥ 6× ratio at step three and
    a ≥ 9× ratio at step five from the Nash Dirac (the worst case).
  • The lumped basins inherit per-player and joint Pareto witnesses
    from `SkyrmsUltraLongRunEquilibrium`, so mass dominance and
    payoff dominance hold simultaneously on the same state space.

It does **not** say:

  • "Every irreducible kernel with positive ULR-bias has long-run
    occupation measure on ULR strictly exceeding that on Nash." That
    universal claim is the genuine ergodic-stationary theorem; it
    requires real-valued limits (`lim_{n→∞}`), Markov-chain
    convergence, and Perron-Frobenius spectral arguments not
    available in Init Lean.
  • Anything about *the* long-run occupation measure, because in
    Init-only Lean we cannot take real limits.

The forward bridge to a future Mathlib lift is the predicate triple
`Irreducible`, `UlrAttractive`, `NashLeaky`. A measure-theoretic
upgrade can quote these exact predicates verbatim as the hypotheses of
the limit theorem; the names will line up, and the discrete witnesses
proved here will become finite-time approximations that subsume into
the genuine `lim` statement once the analytic infrastructure exists.

## Next exploration

`Gnosis/SkyrmsErgodicSelectionMatrix.lean` — generalize the three-basin
lumped kernel to a finite-state kernel indexed by the seven
`PolarizationState` snapshots along
`SkyrmsUltraLongRunEquilibrium.iterate 0..6 nashPolarizationTrap`,
keeping the same `Irreducible`/`UlrAttractive`/`NashLeaky` predicates
but at the un-lumped resolution. The natural target: prove that the
absorbing-rate of the ULR snapshot dominates each non-ULR snapshot's
escape rate row-wise, exposing a finite-state Lyapunov function
(`polarization` itself) without needing a stationary distribution.
That keeps the next discrete bite honest in Init Lean while moving
closer to the spectral structure a Mathlib lift would need.
-/

end SkyrmsErgodicSelection
