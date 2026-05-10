/-
  BowlMeshPinkNoiseBound.lean
  ===========================

  Third leg of the bowl-mesh formalization (siblings:
  `Gnosis.BowlMeshNode`, `Gnosis.BowlMeshQSweep`).

  ## The conjecture this file pins down

  The bowl-mesh model preserves K=1 argmax fidelity **up to pink noise**
  on the residual stream. The intuition:

  * **White noise** — flat spectral density, every frequency bin equally
    loud. Every bowl's input amplitude on resonance equals its input
    amplitude off resonance, so the bowl's selectivity machinery is
    spending Q on a tied input. The argmax over frequencies is no longer
    determined by the bowl's preference; it is determined by whatever
    structural tie-breaker the routing function happens to expose.
  * **Pink noise (1/f and steeper)** — power concentrates in bands. The
    bowl's resonance window can carve out a single fundamental mode and
    the on-resonance amplitude strictly dominates the off-resonance
    amplitude. The bowl recovers the signal.

  The cutoff between the two regimes is a function of the bowl's Q
  factor: a sharper bowl (high Q, low damping) can resolve a flatter
  spectrum than a blunt one.

  ## What's formalized vs what isn't

  Init has no real-valued geometric mean and no exact Fourier transform.
  This module captures the algebraic invariant lattice of the white-vs-
  pink dichotomy with the **simplest possible** `Nat × Nat` ratio:

      flatness = listMin amplitudes / listMax amplitudes

  This is a strictly weaker statistic than the standard spectral-flatness
  measure (geometric mean / arithmetic mean), but it preserves the two
  boundary cases the conjecture turns on:

  * `flatness = 1`  ↔  `listMin = listMax`  ↔  every bin equal — white-flat.
  * `flatness < 1`  ↔  `listMin < listMax`  ↔  at least one strictly
    dominant bin — pink-structured.

  The four theorems below are structural witnesses, not physical-spectrum
  claims. We never assert that the runtime extractor measures this
  particular flatness statistic; we only show that the bowl's behavior
  partitions cleanly along the algebraic dichotomy it does measure. This
  is the same honesty mode `Gnosis.ThoughtBowlMechanics` operates in.

  ## The four theorems

  * `flatness_dichotomy` — every nonempty profile is either white-flat or
    pink-structured. (Direct corollary of `listMin ≤ listMax`.)
  * `white_flat_argmax_ambiguous` — under white-flat input, two distinct
    frequencies that are equidistant from the bowl's fundamental mode
    receive the same route_through_bowl output. The bowl cannot prefer
    one over the other; the argmax is structurally tied.
  * `pink_structured_argmax_recovers` — when the spectrum has a dominant
    bin AT the bowl's fundamental mode AND the bowl has `qFactor ≥ 1`,
    the on-resonance route output is at least the dominant amplitude
    (no information loss at the carrier).
  * `bowl_recovers_below_flatness_threshold` — existence of a flatness
    threshold, constructed from the bowl's Q factor, below which the
    on-resonance output strictly exceeds the off-resonance output.
    The threshold is a witness; we do not claim it is tight.

  Imports `Init` plus the bowl-mesh stack. Zero `sorry`, zero new
  `axiom`.
-/

import Init
import Gnosis.EchoChamberAsTaoBowl
import Gnosis.TaoBowlSignalCoupling
import Gnosis.BowlMeshNode

namespace BowlMeshPinkNoiseBound

open EchoChamberAsTaoBowl
open TaoBowlSignalCoupling
open BowlMeshNode

/-! ## Spectral profile -/

/-- A finite spectrum, bin-indexed by list position. `amplitudes[i]` is
    the energy in bin `i`. We require non-emptiness so that `listMin`
    and `listMax` are pinned to actual bins, not the `Nat` identity of
    the empty fold. -/
structure SpectralProfile where
  amplitudes : List Nat
  nonempty : 0 < amplitudes.length
  deriving Repr

/-- Recursive min over a list. Returns 0 on empty (sentinel; the
    `SpectralProfile.nonempty` field rules this case out at the type
    level for spectra). -/
def listMin : List Nat → Nat
  | [] => 0
  | [x] => x
  | x :: y :: ys => Nat.min x (listMin (y :: ys))

/-- Recursive max over a list. Returns 0 on empty. -/
def listMax : List Nat → Nat
  | [] => 0
  | x :: xs => Nat.max x (listMax xs)

/-- Spectral flatness numerator: the smallest amplitude in the
    spectrum. -/
def flatness_num (sp : SpectralProfile) : Nat :=
  listMin sp.amplitudes

/-- Spectral flatness denominator: the largest amplitude in the
    spectrum. The flatness ratio is `flatness_num / flatness_den`,
    bounded in `[0, 1]` for any non-empty spectrum. -/
def flatness_den (sp : SpectralProfile) : Nat :=
  listMax sp.amplitudes

/-- White-flat: every bin has equal amplitude. Equivalent to
    `flatness = 1` once the ratio is read as a rational. -/
def IsWhiteFlat (sp : SpectralProfile) : Prop :=
  flatness_num sp = flatness_den sp

/-- Pink-structured: at least one bin strictly dominates the minimum.
    Equivalent to `flatness < 1`. -/
def IsPinkStructured (sp : SpectralProfile) : Prop :=
  flatness_num sp < flatness_den sp

/-! ## listMin ≤ listMax (the structural invariant) -/

/-- Every element of a list is at most the list's max. -/
theorem listMax_ge_head (x : Nat) (xs : List Nat) :
    x ≤ listMax (x :: xs) := by
  unfold listMax
  exact Nat.le_max_left _ _

/-- The min of a non-empty list is bounded by its head — and so by the
    max. This is the load-bearing inequality that drives the dichotomy. -/
theorem listMin_le_head (x : Nat) (xs : List Nat) :
    listMin (x :: xs) ≤ x := by
  cases xs with
  | nil =>
      unfold listMin
      exact Nat.le_refl _
  | cons y ys =>
      unfold listMin
      exact Nat.min_le_left _ _

/-- For a non-empty list, `listMin ≤ listMax`. The non-emptiness is
    essential — the empty-list sentinels would otherwise vacuously
    satisfy this with `0 ≤ 0`, which is true but uninformative. -/
theorem listMin_le_listMax : ∀ (xs : List Nat), 0 < xs.length →
    listMin xs ≤ listMax xs := by
  intro xs hpos
  cases xs with
  | nil =>
      -- Vacuous: 0 < 0 is false.
      exact absurd hpos (Nat.lt_irrefl 0)
  | cons x xs' =>
      exact Nat.le_trans (listMin_le_head x xs') (listMax_ge_head x xs')

/-! ## The dichotomy -/

/-- Theorem: every spectrum is either white-flat or pink-structured.
    Direct consequence of `listMin ≤ listMax` and trichotomy on `Nat`. -/
theorem flatness_dichotomy (sp : SpectralProfile) :
    IsWhiteFlat sp ∨ IsPinkStructured sp := by
  unfold IsWhiteFlat IsPinkStructured flatness_num flatness_den
  have hle : listMin sp.amplitudes ≤ listMax sp.amplitudes :=
    listMin_le_listMax sp.amplitudes sp.nonempty
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exact Or.inr hlt
  · exact Or.inl heq

/-! ## White-flat: route output is structurally tied

When the spectrum is white-flat (`listMin = listMax`), any two bins carry
the **same amplitude**. We do not need to inspect the bowl machinery to
see that the route function returns the same output on two equal inputs
at frequencies sharing the same mismatch class: `route_through_bowl` is
a deterministic function of `(freq, amp)`, and white-flat input pins
amp to a single value.

The theorem below states the **structural** form: for any two
frequencies that are both off-resonance, equal amplitude routes to equal
output. The argmax over frequencies cannot prefer one over the other.

This is intentionally a weaker claim than "the bowl is useless under
white noise" — we are not asserting absolute uselessness, only that the
bowl loses its discriminating role between any two off-resonance bins
with tied input. The strong claim would require quantifying over all
frequencies, which Init-Lean's lack of bounded `Fin` machinery makes
clunky. The structural tie is the load-bearing piece for the K=1 argmax
conjecture. -/

theorem white_flat_argmax_ambiguous (n : BowlMeshNode) (sp : SpectralProfile)
    (_h_white : IsWhiteFlat sp) (a : Nat)
    (f₁ f₂ : Nat)
    (hmiss₁ : freqMismatch n.bowl f₁ ≠ 0)
    (hmiss₂ : freqMismatch n.bowl f₂ ≠ 0) :
    route_through_bowl n f₁ a = route_through_bowl n f₂ a := by
  -- Off-mode branch is `a / (damping + 1)` regardless of frequency.
  -- The white-flat hypothesis ensures the inputs are not differentiated
  -- by amplitude; here we additionally use that route depends only on
  -- amp once we are in the off-mode branch.
  unfold route_through_bowl filteredAmplitude
  -- The white-flat hypothesis is not consumed in the proof because
  -- the off-mode arithmetic is already amplitude-and-damping-only;
  -- including it in the statement keeps the theorem read consistently
  -- with the white-flat regime that motivates it.
  rw [if_neg hmiss₁, if_neg hmiss₂]

/-! ## Pink-structured: on-resonance carrier survives

When the spectrum has a dominant bin (`listMin < listMax`) and that bin
sits **at** the bowl's fundamental mode, the bowl's on-resonance branch
fires:

    filteredAmplitude bowl f amp = amp * qFactor bowl   (when mismatch = 0)

If additionally `qFactor ≥ 1`, the output is at least the input
amplitude. The dominant bin's energy is not lost at the carrier.

We thread the dominant amplitude through `listMax` as a witness; the
bowl returns at least that amplitude. -/

theorem pink_structured_argmax_recovers (n : BowlMeshNode) (sp : SpectralProfile)
    (_h_pink : IsPinkStructured sp)
    (f : Nat)
    (h_on_mode : freqMismatch n.bowl f = 0)
    (h_q : 1 ≤ qFactor n.bowl) :
    flatness_den sp ≤ route_through_bowl n f (flatness_den sp) := by
  -- On-mode: route = amp * qFactor. With qFactor ≥ 1, amp ≤ amp * qFactor.
  unfold route_through_bowl filteredAmplitude
  rw [if_pos h_on_mode]
  -- Goal: flatness_den sp ≤ flatness_den sp * qFactor n.bowl
  -- Cast LHS as `_ * 1` and chain through mul-monotonicity on the right.
  calc flatness_den sp
      = flatness_den sp * 1 := (Nat.mul_one _).symm
    _ ≤ flatness_den sp * qFactor n.bowl :=
        Nat.mul_le_mul_left (flatness_den sp) h_q

/-! ## On-resonance strictly dominates off-resonance below a threshold

The conjectured "flatness threshold" claim: there exists a flatness
configuration below which the on-resonance bin's bowl output strictly
exceeds the off-resonance bin's bowl output. We construct a witness
threshold from the bowl's parameters and exhibit a concrete spectrum
that beats it.

Because Init-Lean does not give us a clean rational-threshold inequality
to reason against (and because `flatness` is a *ratio*, not a number we
can directly compare to a single threshold without rational arithmetic),
we encode the existence claim as a paired witness: a concrete profile
that is pink-structured **and** whose dominant bin's bowl output
strictly exceeds the bowl output of its minimum bin (the worst off-
resonance bin). The witness uses `balancedBowlNode` to anchor parameters.

This is weaker than the contract sketch's universal-quantifier form, but
it is the honest existence statement — we are not in a position to
universally quantify over a real-valued threshold in Init-Lean. -/

/-- Concrete witness profile: amplitudes `[1, 100]`. `listMin = 1`,
    `listMax = 100`, so it is strictly pink-structured. -/
def witnessProfile : SpectralProfile where
  amplitudes := [1, 100]
  nonempty := by decide

theorem witnessProfile_is_pink :
    IsPinkStructured witnessProfile := by
  unfold IsPinkStructured flatness_num flatness_den witnessProfile listMin listMax
  decide

/-- Existence of a flatness threshold below which the bowl's on-
    resonance output strictly exceeds its off-resonance output. The
    threshold is encoded structurally: we exhibit a pink-structured
    profile and a bowl-node configuration at which the strict
    domination holds. -/
theorem bowl_recovers_below_flatness_threshold :
    ∃ (sp : SpectralProfile) (n : BowlMeshNode) (f_on f_off : Nat),
      IsPinkStructured sp ∧
      freqMismatch n.bowl f_on = 0 ∧
      freqMismatch n.bowl f_off ≠ 0 ∧
      route_through_bowl n f_off (flatness_num sp)
        < route_through_bowl n f_on (flatness_den sp) := by
  refine ⟨witnessProfile, balancedBowlNode, 3, 10, ?_, ?_, ?_, ?_⟩
  · exact witnessProfile_is_pink
  · -- balancedBowl fundamentalMode = 3, so freqMismatch _ 3 = 0
    unfold balancedBowlNode
    show freqMismatch balancedBowl 3 = 0
    exact on_mode_signal_has_zero_mismatch
  · -- freqMismatch balancedBowl 10 ≠ 0
    unfold balancedBowlNode
    show freqMismatch balancedBowl 10 ≠ 0
    unfold freqMismatch fundamentalMode balancedBowl
    decide
  · -- route through bowl: off-mode at amp = listMin = 1 vs on-mode at amp = listMax = 100
    -- Off-mode: 1 / (damping + 1) = 1 / 2 = 0
    -- On-mode:  100 * qFactor(balancedBowl) = 100 * (5*3/1) = 100 * 15 = 1500
    -- So 0 < 1500.
    unfold route_through_bowl filteredAmplitude balancedBowlNode flatness_num flatness_den
      witnessProfile listMin listMax
    decide

/-! ## Honesty note

The spectral-flatness statistic used here (`listMin / listMax`) is
**not** the standard spectral-flatness measure (geometric mean over
arithmetic mean). Init has no real-valued nth root, so the standard
measure is unreachable. The simpler ratio still cleanly partitions the
two boundary cases the bowl conjecture cares about — white-flat
(`min = max`) and pink-structured (`min < max`) — and that's the
algebraic invariant lattice the theorems witness.

We do not claim that any runtime spectrum-flatness measurement
corresponds to this statistic. We do not claim that the witness
threshold in `bowl_recovers_below_flatness_threshold` is tight. The
load-bearing pieces are:

* the dichotomy is exhaustive (`flatness_dichotomy`),
* the white-flat regime ties the bowl's off-resonance output across
  frequencies (`white_flat_argmax_ambiguous`),
* the pink-structured regime preserves the on-resonance amplitude
  when the bowl has `qFactor ≥ 1` (`pink_structured_argmax_recovers`),
* a concrete witness shows the strict domination is reachable
  (`bowl_recovers_below_flatness_threshold`).

The same honesty mode `Gnosis.ThoughtBowlMechanics` operates in:
faithful on the algebraic invariant lattice, silent on physical
spectrum semantics.
-/

end BowlMeshPinkNoiseBound
