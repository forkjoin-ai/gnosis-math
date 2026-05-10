/-
  DepolarizationIsParetoImprovement.lean
  ======================================

  Thesis: **depolarization and Pareto-improvement are the same
  dynamic** under the Skyrms-ULR mutation kernel — and that dynamic
  is *also* the American Frontier closing its topological deficit
  in three-face Bule vocabulary.

  ## Reading the equivalence

  We work on the canonical six-step Nash → ULR mutation path
  established in `SkyrmsUltraLongRunEquilibrium`. The six steps
  decompose into two regimes:

  * **Depolarization phase (steps 0 → 5).** Polarization strictly
    decreases by 2 each step. Joint welfare strictly increases by 2
    each step. Each per-player payoff strictly increases. Every
    step is simultaneously
    `IsDepolarizationStep`,
    `IsJointWelfareImprovement`, and
    `IsParetoImprovement`.

  * **Welfare-completion phase (step 5 → 6).** Polarization is
    already saturated at 0 and stays there. Joint welfare strictly
    increases by 2 (debts complete their drop to the cooperative
    floor). Pareto-improvement continues without further
    depolarization.

  This phase decomposition is what makes the slogan
  "depolarization is Pareto-improvement" technically subtle: on the
  depolarization phase the two are coupled step-for-step, but
  Pareto-improvement is a *strictly larger* dynamic that extends
  past depolarization saturation. Depolarization is *sufficient*
  for Pareto-improvement on this kernel; it is not necessary.
  The honest theorem is `depolarization_implies_pareto_on_kernel`
  and the honest non-equivalence is
  `pareto_can_continue_past_depolarization`.

  ## Three-face Bule reading

  Encode each `PolarizationState` as a `BuleyUnit` via
  `frontierBule` with the substitution
    `streams := budget − polarization`,
  which yields:
    `waste = polarization`,
    `opportunity = polarization`,
    `diversity = budget − polarization`.

  Each depolarization step is then exactly a
  `BuleThreeFaceOptimalMove`: waste contracts, opportunity
  contracts, diversity expands. The structural shape of "Pareto-
  improving co-ordination" is the structural shape of "closing the
  three-face Bule deficit." That is the Bule reading of the same
  dynamic.

  ## American Frontier bridge

  Under the Bule encoding, the Nash polarization trap is
  *pre-frontier* (positive waste, brown-noise regime), the
  intermediate states are progressively closer to the frontier,
  and the Skyrms ULR fixed point is *at-frontier* (zero waste,
  pink-noise regime). The mutation kernel marches through the
  three-regime ledger: brown → pink. Depolarization in payoff
  vocabulary, Pareto-improvement in welfare vocabulary, and
  frontier-closure in transport vocabulary are three projections
  of one mechanism.

  ## Five-fold lift and the conservation law

  The 3-face Bule reading exhibits a **conservation law** during
  the depolarization phase:
    `threeFaceBuleValue + jointWelfare = 26`  (steps 0..5)
  The kernel converts polarization-mass into welfare-mass
  one-for-one: each unit of polarization spent is exactly one unit
  of welfare gained. The 3-face Bule curve cannot represent the
  post-depolarization welfare gain; the 5-fold lift via
  `visibleOnlyFiveFold` gives a coordinate system where that gain
  appears as a strict increase in the combined value at step 6.

  This is the precise sense in which the 3-face Bule is the
  *visible* projection of a five-fold carrier: the mutation kernel
  conserves the visible projection during depolarization but adds
  value via a coordinate the visible projection cannot see during
  welfare-completion.

  ## Honesty boundary

  All quantitative claims are at the `Nat` kernel level on the
  concrete six-step path. The general claim "any kernel that
  depolarizes Pareto-improves" is *not* proved here; that requires
  measure-theoretic stochastic-stability machinery that
  `Gnosis.SkyrmsUltraLongRunEquilibrium` already disclaims. What
  *is* proved here is the conditional, kernel-bound version of the
  thesis, plus the structural Bule and American-Frontier readings.

  Imports `Gnosis.SkyrmsUltraLongRunEquilibrium`,
  `Gnosis.BuleIsValue`, `Gnosis.AmericanFrontier`. Zero `sorry`,
  zero new `axiom`.
-/

import Gnosis.SkyrmsUltraLongRunEquilibrium
import Gnosis.BuleIsValue
import Gnosis.AmericanFrontier

namespace DepolarizationIsParetoImprovement

open SkyrmsUltraLongRunEquilibrium
  (PolarizationState polarization jointWelfare payoffAOf payoffBOf
   nashPolarizationTrap skyrmsUltraLongRunFixedPoint
   mutationStep iterate)
open Gnosis (BuleThreeFaceOptimalMove buleTotalValue
             buleWasteValue buleOpportunityValue buleDiversityValue
             frontierBule frontierStreamCount AtFrontier
             FrontierRegime frontierRegime frontierNoise
             visibleOnlyFiveFold visibleBuleProjection
             buleFiveFoldValue darkInterferenceLoad)
open Gnosis.SpectralNoiseEquilibrium (BuleyUnit)

/-! ## Coupling predicates -/

/-- Strict depolarization: inter-agent positional spread strictly
    decreases. -/
def IsDepolarizationStep (s s' : PolarizationState) : Prop :=
  polarization s' < polarization s

/-- Strict joint-welfare improvement: the sum of per-player payoffs
    strictly increases. -/
def IsJointWelfareImprovement (s s' : PolarizationState) : Prop :=
  jointWelfare s < jointWelfare s'

/-- Strict per-player Pareto-improvement: every player's payoff
    strictly increases. (Stronger than the weak-Pareto reading;
    we use the strong form because the kernel actually delivers it.) -/
def IsStrictParetoImprovement (s s' : PolarizationState) : Prop :=
  payoffAOf s < payoffAOf s' ∧ payoffBOf s < payoffBOf s'

/-! ## Per-step witnesses on the depolarization phase

The first five steps of the canonical Nash → ULR path are *each*
simultaneously a depolarization step, a joint-welfare improvement,
and a strict per-player Pareto improvement. Each witness reduces
to a `Nat` computation under `native_decide`.
-/

theorem step_zero_to_one_couples_depolarization_and_pareto :
    IsDepolarizationStep (iterate 0 nashPolarizationTrap)
        (iterate 1 nashPolarizationTrap) ∧
    IsJointWelfareImprovement (iterate 0 nashPolarizationTrap)
        (iterate 1 nashPolarizationTrap) ∧
    IsStrictParetoImprovement (iterate 0 nashPolarizationTrap)
        (iterate 1 nashPolarizationTrap) := by
  unfold IsDepolarizationStep IsJointWelfareImprovement
    IsStrictParetoImprovement polarization jointWelfare
    payoffAOf payoffBOf iterate mutationStep nashPolarizationTrap
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

theorem step_one_to_two_couples_depolarization_and_pareto :
    IsDepolarizationStep (iterate 1 nashPolarizationTrap)
        (iterate 2 nashPolarizationTrap) ∧
    IsJointWelfareImprovement (iterate 1 nashPolarizationTrap)
        (iterate 2 nashPolarizationTrap) ∧
    IsStrictParetoImprovement (iterate 1 nashPolarizationTrap)
        (iterate 2 nashPolarizationTrap) := by
  unfold IsDepolarizationStep IsJointWelfareImprovement
    IsStrictParetoImprovement polarization jointWelfare
    payoffAOf payoffBOf iterate mutationStep nashPolarizationTrap
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

theorem step_two_to_three_couples_depolarization_and_pareto :
    IsDepolarizationStep (iterate 2 nashPolarizationTrap)
        (iterate 3 nashPolarizationTrap) ∧
    IsJointWelfareImprovement (iterate 2 nashPolarizationTrap)
        (iterate 3 nashPolarizationTrap) ∧
    IsStrictParetoImprovement (iterate 2 nashPolarizationTrap)
        (iterate 3 nashPolarizationTrap) := by
  unfold IsDepolarizationStep IsJointWelfareImprovement
    IsStrictParetoImprovement polarization jointWelfare
    payoffAOf payoffBOf iterate mutationStep nashPolarizationTrap
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

theorem step_three_to_four_couples_depolarization_and_pareto :
    IsDepolarizationStep (iterate 3 nashPolarizationTrap)
        (iterate 4 nashPolarizationTrap) ∧
    IsJointWelfareImprovement (iterate 3 nashPolarizationTrap)
        (iterate 4 nashPolarizationTrap) ∧
    IsStrictParetoImprovement (iterate 3 nashPolarizationTrap)
        (iterate 4 nashPolarizationTrap) := by
  unfold IsDepolarizationStep IsJointWelfareImprovement
    IsStrictParetoImprovement polarization jointWelfare
    payoffAOf payoffBOf iterate mutationStep nashPolarizationTrap
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

theorem step_four_to_five_couples_depolarization_and_pareto :
    IsDepolarizationStep (iterate 4 nashPolarizationTrap)
        (iterate 5 nashPolarizationTrap) ∧
    IsJointWelfareImprovement (iterate 4 nashPolarizationTrap)
        (iterate 5 nashPolarizationTrap) ∧
    IsStrictParetoImprovement (iterate 4 nashPolarizationTrap)
        (iterate 5 nashPolarizationTrap) := by
  unfold IsDepolarizationStep IsJointWelfareImprovement
    IsStrictParetoImprovement polarization jointWelfare
    payoffAOf payoffBOf iterate mutationStep nashPolarizationTrap
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **The depolarization phase, packaged.** Every off-fixed-point
    step in the depolarization regime is simultaneously
    depolarization, joint-welfare improvement, and per-player
    strict Pareto improvement. -/
theorem depolarization_phase_couples_pareto :
    (IsDepolarizationStep (iterate 0 nashPolarizationTrap)
        (iterate 1 nashPolarizationTrap) ∧
      IsJointWelfareImprovement (iterate 0 nashPolarizationTrap)
        (iterate 1 nashPolarizationTrap) ∧
      IsStrictParetoImprovement (iterate 0 nashPolarizationTrap)
        (iterate 1 nashPolarizationTrap)) ∧
    (IsDepolarizationStep (iterate 1 nashPolarizationTrap)
        (iterate 2 nashPolarizationTrap) ∧
      IsJointWelfareImprovement (iterate 1 nashPolarizationTrap)
        (iterate 2 nashPolarizationTrap) ∧
      IsStrictParetoImprovement (iterate 1 nashPolarizationTrap)
        (iterate 2 nashPolarizationTrap)) ∧
    (IsDepolarizationStep (iterate 2 nashPolarizationTrap)
        (iterate 3 nashPolarizationTrap) ∧
      IsJointWelfareImprovement (iterate 2 nashPolarizationTrap)
        (iterate 3 nashPolarizationTrap) ∧
      IsStrictParetoImprovement (iterate 2 nashPolarizationTrap)
        (iterate 3 nashPolarizationTrap)) ∧
    (IsDepolarizationStep (iterate 3 nashPolarizationTrap)
        (iterate 4 nashPolarizationTrap) ∧
      IsJointWelfareImprovement (iterate 3 nashPolarizationTrap)
        (iterate 4 nashPolarizationTrap) ∧
      IsStrictParetoImprovement (iterate 3 nashPolarizationTrap)
        (iterate 4 nashPolarizationTrap)) ∧
    (IsDepolarizationStep (iterate 4 nashPolarizationTrap)
        (iterate 5 nashPolarizationTrap) ∧
      IsJointWelfareImprovement (iterate 4 nashPolarizationTrap)
        (iterate 5 nashPolarizationTrap) ∧
      IsStrictParetoImprovement (iterate 4 nashPolarizationTrap)
        (iterate 5 nashPolarizationTrap)) :=
  ⟨step_zero_to_one_couples_depolarization_and_pareto,
   step_one_to_two_couples_depolarization_and_pareto,
   step_two_to_three_couples_depolarization_and_pareto,
   step_three_to_four_couples_depolarization_and_pareto,
   step_four_to_five_couples_depolarization_and_pareto⟩

/-! ## The honest non-equivalence: Pareto continues past depolarization

At step 5 the polarization measure has saturated at 0 (positions
have already met at the median) but debt has one more step left.
The 5 → 6 transition is therefore Pareto-improving without being
depolarizing. This is the formal mirror of the slogan caveat:
*"depolarization implies Pareto-improvement on this kernel; Pareto-
improvement is a strictly larger dynamic."*
-/

theorem step_five_to_six_is_pareto_without_depolarization :
    ¬ IsDepolarizationStep (iterate 5 nashPolarizationTrap)
        (iterate 6 nashPolarizationTrap) ∧
    IsJointWelfareImprovement (iterate 5 nashPolarizationTrap)
        (iterate 6 nashPolarizationTrap) ∧
    IsStrictParetoImprovement (iterate 5 nashPolarizationTrap)
        (iterate 6 nashPolarizationTrap) := by
  unfold IsDepolarizationStep IsJointWelfareImprovement
    IsStrictParetoImprovement polarization jointWelfare
    payoffAOf payoffBOf iterate mutationStep nashPolarizationTrap
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **Pareto-improvement is strictly larger than depolarization.**
    On this kernel, every depolarization step Pareto-improves, but
    a Pareto-improving step need not depolarize. -/
theorem pareto_can_continue_past_depolarization :
    ∃ s s' : PolarizationState,
      ¬ IsDepolarizationStep s s' ∧
      IsJointWelfareImprovement s s' ∧
      IsStrictParetoImprovement s s' :=
  ⟨iterate 5 nashPolarizationTrap, iterate 6 nashPolarizationTrap,
   step_five_to_six_is_pareto_without_depolarization⟩

/-! ## The forward implication: depolarization ⇒ Pareto on kernel -/

/-- The witness function selecting the right per-step theorem for
    each `k ∈ {0, 1, 2, 3, 4}`. -/
private def stepWitness (k : Fin 5) :
    IsJointWelfareImprovement (iterate k.val nashPolarizationTrap)
      (iterate (k.val + 1) nashPolarizationTrap) ∧
    IsStrictParetoImprovement (iterate k.val nashPolarizationTrap)
      (iterate (k.val + 1) nashPolarizationTrap) :=
  match k with
  | ⟨0, _⟩ =>
      ⟨step_zero_to_one_couples_depolarization_and_pareto.2.1,
       step_zero_to_one_couples_depolarization_and_pareto.2.2⟩
  | ⟨1, _⟩ =>
      ⟨step_one_to_two_couples_depolarization_and_pareto.2.1,
       step_one_to_two_couples_depolarization_and_pareto.2.2⟩
  | ⟨2, _⟩ =>
      ⟨step_two_to_three_couples_depolarization_and_pareto.2.1,
       step_two_to_three_couples_depolarization_and_pareto.2.2⟩
  | ⟨3, _⟩ =>
      ⟨step_three_to_four_couples_depolarization_and_pareto.2.1,
       step_three_to_four_couples_depolarization_and_pareto.2.2⟩
  | ⟨4, _⟩ =>
      ⟨step_four_to_five_couples_depolarization_and_pareto.2.1,
       step_four_to_five_couples_depolarization_and_pareto.2.2⟩

/-- **Depolarization is sufficient for Pareto-improvement under
    the kernel.** Every depolarization step on the canonical
    Nash → ULR path is a strict joint-welfare improvement and a
    strict per-player Pareto improvement. -/
theorem depolarization_implies_pareto_on_kernel
    (k : Fin 5) :
    IsDepolarizationStep (iterate k.val nashPolarizationTrap)
        (iterate (k.val + 1) nashPolarizationTrap) →
      IsJointWelfareImprovement (iterate k.val nashPolarizationTrap)
        (iterate (k.val + 1) nashPolarizationTrap) ∧
      IsStrictParetoImprovement (iterate k.val nashPolarizationTrap)
        (iterate (k.val + 1) nashPolarizationTrap) := by
  intro _hDep
  exact stepWitness k

/-! ## 3-face Bule encoding -/

/-- Polarization state read as a transport-side stream count: the
    "depolarization progress" toward full coordination.

    `streams := budget − polarization`. The Nash trap has zero
    streams (no coordination); the ULR has full streams (frontier
    coordination); intermediate states interpolate. -/
def coordinationStreams (s : PolarizationState) : Nat :=
  s.budget - polarization s

/-- The polarization state lifted into the three-face Bule curve
    via the American-Frontier encoding. The substitution
    `streams := budget − polarization` produces:
    `waste = polarization`,
    `opportunity = polarization`,
    `diversity = budget − polarization = streams`. -/
def threeFaceBule (s : PolarizationState) : BuleyUnit :=
  frontierBule s.budget (coordinationStreams s)

/-- Total 3-face Bule value across waste, opportunity, and
    diversity. -/
def threeFaceBuleValue (s : PolarizationState) : Nat :=
  buleTotalValue (threeFaceBule s)

theorem nash_trap_three_face_bule :
    threeFaceBule nashPolarizationTrap = ⟨10, 10, 0⟩ := by
  unfold threeFaceBule coordinationStreams polarization
    nashPolarizationTrap frontierBule frontierStreamCount
  decide

theorem ulr_three_face_bule :
    threeFaceBule skyrmsUltraLongRunFixedPoint = ⟨0, 0, 10⟩ := by
  unfold threeFaceBule coordinationStreams polarization
    skyrmsUltraLongRunFixedPoint frontierBule frontierStreamCount
  decide

theorem nash_trap_three_face_value_eq_twenty :
    threeFaceBuleValue nashPolarizationTrap = 20 := by
  unfold threeFaceBuleValue buleTotalValue
  rw [nash_trap_three_face_bule]
  decide

theorem ulr_three_face_value_eq_ten :
    threeFaceBuleValue skyrmsUltraLongRunFixedPoint = 10 := by
  unfold threeFaceBuleValue buleTotalValue
  rw [ulr_three_face_bule]
  decide

/-! ## Each depolarization step is a Bule three-face optimal move -/

theorem step_zero_to_one_is_bule_optimal :
    BuleThreeFaceOptimalMove
      (threeFaceBule (iterate 0 nashPolarizationTrap))
      (threeFaceBule (iterate 1 nashPolarizationTrap)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (unfold threeFaceBule coordinationStreams polarization
      iterate mutationStep nashPolarizationTrap frontierBule
      frontierStreamCount; native_decide)

theorem step_one_to_two_is_bule_optimal :
    BuleThreeFaceOptimalMove
      (threeFaceBule (iterate 1 nashPolarizationTrap))
      (threeFaceBule (iterate 2 nashPolarizationTrap)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (unfold threeFaceBule coordinationStreams polarization
      iterate mutationStep nashPolarizationTrap frontierBule
      frontierStreamCount; native_decide)

theorem step_two_to_three_is_bule_optimal :
    BuleThreeFaceOptimalMove
      (threeFaceBule (iterate 2 nashPolarizationTrap))
      (threeFaceBule (iterate 3 nashPolarizationTrap)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (unfold threeFaceBule coordinationStreams polarization
      iterate mutationStep nashPolarizationTrap frontierBule
      frontierStreamCount; native_decide)

theorem step_three_to_four_is_bule_optimal :
    BuleThreeFaceOptimalMove
      (threeFaceBule (iterate 3 nashPolarizationTrap))
      (threeFaceBule (iterate 4 nashPolarizationTrap)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (unfold threeFaceBule coordinationStreams polarization
      iterate mutationStep nashPolarizationTrap frontierBule
      frontierStreamCount; native_decide)

theorem step_four_to_five_is_bule_optimal :
    BuleThreeFaceOptimalMove
      (threeFaceBule (iterate 4 nashPolarizationTrap))
      (threeFaceBule (iterate 5 nashPolarizationTrap)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (unfold threeFaceBule coordinationStreams polarization
      iterate mutationStep nashPolarizationTrap frontierBule
      frontierStreamCount; native_decide)

/-- **Honest negative.** The post-depolarization step (5 → 6) is
    *not* a `BuleThreeFaceOptimalMove`: waste, opportunity, and
    diversity all stay constant because polarization is already
    zero. The 3-face Bule curve cannot see the welfare gain that
    happens here — that information lives in the dark coordinates
    of the 5-fold lift. -/
theorem step_five_to_six_is_not_bule_optimal :
    ¬ BuleThreeFaceOptimalMove
        (threeFaceBule (iterate 5 nashPolarizationTrap))
        (threeFaceBule (iterate 6 nashPolarizationTrap)) := by
  intro h
  have hw := h.waste_contracts
  unfold threeFaceBule coordinationStreams polarization iterate
    mutationStep nashPolarizationTrap frontierBule
    frontierStreamCount at hw
  exact absurd hw (by native_decide)

/-! ## American Frontier bridge -/

/-- The Nash polarization trap sits *pre-frontier*: positive waste,
    brown-noise regime. Coordination is missing. -/
theorem nash_trap_is_pre_frontier :
    coordinationStreams nashPolarizationTrap <
      frontierStreamCount nashPolarizationTrap.budget := by
  unfold coordinationStreams polarization nashPolarizationTrap
    frontierStreamCount
  decide

/-- The Skyrms ULR fixed point sits *at-frontier*: zero waste, pink
    contact-turbulence regime. Coordination is exact. -/
theorem ulr_is_at_frontier :
    AtFrontier skyrmsUltraLongRunFixedPoint.budget
      (coordinationStreams skyrmsUltraLongRunFixedPoint) := by
  unfold AtFrontier coordinationStreams polarization
    skyrmsUltraLongRunFixedPoint frontierStreamCount
  decide

/-- The Nash trap is brown-noise (pre-frontier under-coordination). -/
theorem nash_trap_frontier_regime_is_brown :
    frontierNoise (frontierRegime nashPolarizationTrap.budget
      (coordinationStreams nashPolarizationTrap))
      = Gnosis.NoiseLedger.brown_noise := by
  unfold frontierRegime coordinationStreams polarization
    nashPolarizationTrap frontierStreamCount frontierNoise
  decide

/-- The Skyrms ULR is pink-noise (at-frontier contact turbulence). -/
theorem ulr_frontier_regime_is_pink :
    frontierNoise (frontierRegime skyrmsUltraLongRunFixedPoint.budget
      (coordinationStreams skyrmsUltraLongRunFixedPoint))
      = Gnosis.NoiseLedger.pink_noise := by
  unfold frontierRegime coordinationStreams polarization
    skyrmsUltraLongRunFixedPoint frontierStreamCount frontierNoise
  decide

/-- Per-step witnesses for single-stream advance toward the frontier
    on the canonical Nash → ULR path. -/
theorem step_zero_to_one_is_frontier_progress :
    coordinationStreams (iterate 0 nashPolarizationTrap) <
      coordinationStreams (iterate 1 nashPolarizationTrap) := by
  unfold coordinationStreams polarization iterate mutationStep
    nashPolarizationTrap
  native_decide

theorem step_one_to_two_is_frontier_progress :
    coordinationStreams (iterate 1 nashPolarizationTrap) <
      coordinationStreams (iterate 2 nashPolarizationTrap) := by
  unfold coordinationStreams polarization iterate mutationStep
    nashPolarizationTrap
  native_decide

theorem step_two_to_three_is_frontier_progress :
    coordinationStreams (iterate 2 nashPolarizationTrap) <
      coordinationStreams (iterate 3 nashPolarizationTrap) := by
  unfold coordinationStreams polarization iterate mutationStep
    nashPolarizationTrap
  native_decide

theorem step_three_to_four_is_frontier_progress :
    coordinationStreams (iterate 3 nashPolarizationTrap) <
      coordinationStreams (iterate 4 nashPolarizationTrap) := by
  unfold coordinationStreams polarization iterate mutationStep
    nashPolarizationTrap
  native_decide

theorem step_four_to_five_is_frontier_progress :
    coordinationStreams (iterate 4 nashPolarizationTrap) <
      coordinationStreams (iterate 5 nashPolarizationTrap) := by
  unfold coordinationStreams polarization iterate mutationStep
    nashPolarizationTrap
  native_decide

/-- **Frontier-progress identification:** each depolarization step
    is a single-stream advance toward the frontier under the Bule
    encoding. This is the formal sense in which "depolarization,"
    "Pareto-improvement," and "American-Frontier progress" are
    three projections of one mechanism. -/
theorem depolarization_phase_is_frontier_progress :
    coordinationStreams (iterate 0 nashPolarizationTrap) <
      coordinationStreams (iterate 1 nashPolarizationTrap) ∧
    coordinationStreams (iterate 1 nashPolarizationTrap) <
      coordinationStreams (iterate 2 nashPolarizationTrap) ∧
    coordinationStreams (iterate 2 nashPolarizationTrap) <
      coordinationStreams (iterate 3 nashPolarizationTrap) ∧
    coordinationStreams (iterate 3 nashPolarizationTrap) <
      coordinationStreams (iterate 4 nashPolarizationTrap) ∧
    coordinationStreams (iterate 4 nashPolarizationTrap) <
      coordinationStreams (iterate 5 nashPolarizationTrap) :=
  ⟨step_zero_to_one_is_frontier_progress,
   step_one_to_two_is_frontier_progress,
   step_two_to_three_is_frontier_progress,
   step_three_to_four_is_frontier_progress,
   step_four_to_five_is_frontier_progress⟩

/-! ## Conservation law during the depolarization phase -/

/-- The combined ledger that pairs the visible 3-face Bule reading
    with the joint welfare. -/
def combinedLedger (s : PolarizationState) : Nat :=
  threeFaceBuleValue s + jointWelfare s

/-- **Conservation law.** During the depolarization phase
    (steps 0 .. 5), each unit of polarization spent is converted
    one-for-one into joint welfare. The combined ledger
    `threeFaceBuleValue + jointWelfare` is invariant at 26. -/
theorem combined_ledger_invariant_on_depolarization_phase :
    combinedLedger (iterate 0 nashPolarizationTrap) = 26 ∧
    combinedLedger (iterate 1 nashPolarizationTrap) = 26 ∧
    combinedLedger (iterate 2 nashPolarizationTrap) = 26 ∧
    combinedLedger (iterate 3 nashPolarizationTrap) = 26 ∧
    combinedLedger (iterate 4 nashPolarizationTrap) = 26 ∧
    combinedLedger (iterate 5 nashPolarizationTrap) = 26 := by
  unfold combinedLedger threeFaceBuleValue threeFaceBule
    coordinationStreams polarization jointWelfare
    payoffAOf payoffBOf iterate mutationStep nashPolarizationTrap
    frontierBule frontierStreamCount buleTotalValue
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **The post-depolarization break.** At step 5 → 6 the conservation
    law breaks: the combined ledger jumps strictly upward by 2.
    This is the "post-frontier" welfare gain that the visible
    3-face Bule cannot represent — exactly what the 5-fold lift's
    dark coordinates exist for. -/
theorem combined_ledger_breaks_after_depolarization :
    combinedLedger (iterate 6 nashPolarizationTrap)
      = combinedLedger (iterate 5 nashPolarizationTrap) + 2 := by
  unfold combinedLedger threeFaceBuleValue threeFaceBule
    coordinationStreams polarization jointWelfare
    payoffAOf payoffBOf iterate mutationStep nashPolarizationTrap
    frontierBule frontierStreamCount buleTotalValue
  native_decide

/-! ## 5-fold lift: encoding the post-depolarization gain

The visible 3-face Bule reading collapses the welfare-completion
step into a no-op. The 5-fold lift recovers the missing
information by parking the joint welfare in the constructive
interference channel — a coordinate the 3-face projection does
not see.
-/

/-- 5-fold lift of the polarization state: the visible 3-face
    reading projected from `frontierBule`, plus the joint welfare
    parked in the constructive-interference channel and zero
    destructive interference. Combined value
    = threeFace + jointWelfare = `combinedLedger`. -/
def fiveFoldLift (s : PolarizationState) : Gnosis.BuleFiveFold where
  visible := threeFaceBule s
  constructiveInterference := jointWelfare s
  destructiveInterference := 0

theorem visible_projection_of_lift_is_three_face (s : PolarizationState) :
    visibleBuleProjection (fiveFoldLift s) = threeFaceBule s := rfl

theorem dark_load_of_lift_eq_joint_welfare (s : PolarizationState) :
    darkInterferenceLoad (fiveFoldLift s) = jointWelfare s := by
  unfold darkInterferenceLoad fiveFoldLift
  exact Nat.add_zero _

theorem five_fold_value_of_lift_eq_combined_ledger
    (s : PolarizationState) :
    buleFiveFoldValue (fiveFoldLift s) = combinedLedger s := by
  unfold buleFiveFoldValue combinedLedger threeFaceBuleValue
  rw [dark_load_of_lift_eq_joint_welfare]
  rfl

/-- **The 5-fold lift carries the welfare-completion step that the
    3-face projection cannot see.** The visible 3-face value is
    invariant on step 5 → 6, but the 5-fold value strictly
    increases — the gain lives in the constructive-interference
    coordinate. -/
theorem five_fold_value_strictly_grows_at_post_depolarization_step :
    buleFiveFoldValue (fiveFoldLift (iterate 5 nashPolarizationTrap))
      < buleFiveFoldValue (fiveFoldLift (iterate 6 nashPolarizationTrap)) := by
  rw [five_fold_value_of_lift_eq_combined_ledger,
      five_fold_value_of_lift_eq_combined_ledger,
      combined_ledger_breaks_after_depolarization]
  exact Nat.lt_add_of_pos_right (by decide)

/-- The visible projection is invariant on step 5 → 6 (no
    `BuleThreeFaceOptimalMove`), but the 5-fold lift strictly
    grows. This is the precise sense in which the 5-fold extension
    is structurally required to represent the welfare-completion
    phase. -/
theorem visible_invariant_but_five_fold_grows_at_step_five_to_six :
    visibleBuleProjection (fiveFoldLift (iterate 5 nashPolarizationTrap))
        = visibleBuleProjection (fiveFoldLift (iterate 6 nashPolarizationTrap)) ∧
    buleFiveFoldValue (fiveFoldLift (iterate 5 nashPolarizationTrap))
        < buleFiveFoldValue (fiveFoldLift (iterate 6 nashPolarizationTrap)) := by
  refine ⟨?_, five_fold_value_strictly_grows_at_post_depolarization_step⟩
  unfold visibleBuleProjection fiveFoldLift threeFaceBule
    coordinationStreams polarization iterate mutationStep
    nashPolarizationTrap frontierBule frontierStreamCount
  native_decide

/-! ## The thesis, packaged

Three projections of one dynamic — payoff, Bule, frontier — agree
on the depolarization phase and reveal their honest difference at
the welfare-completion step.
-/

/-- **Headline theorem.** On the canonical Nash → ULR path:

    1. Each depolarization step is simultaneously a strict
       joint-welfare improvement *and* a strict per-player Pareto
       improvement *and* a `BuleThreeFaceOptimalMove` *and* a
       single-stream advance toward the American Frontier.
    2. The combined ledger `threeFaceBuleValue + jointWelfare` is
       invariant during depolarization (the conversion is exact).
    3. The post-depolarization step (5 → 6) is Pareto-improving
       but not depolarizing; the 3-face Bule cannot see the gain;
       the 5-fold lift recovers it via the constructive-
       interference coordinate.

    Together these say: depolarization and Pareto-improvement
    coincide on the depolarization phase, and what continues past
    that phase is welfare-completion in the dark coordinates of
    the 5-fold lift. -/
theorem depolarization_is_pareto_improvement_full_thesis :
    -- (1a) The canonical depolarization-phase coupling
    (IsDepolarizationStep (iterate 0 nashPolarizationTrap)
        (iterate 1 nashPolarizationTrap) ∧
      IsJointWelfareImprovement (iterate 0 nashPolarizationTrap)
        (iterate 1 nashPolarizationTrap) ∧
      IsStrictParetoImprovement (iterate 0 nashPolarizationTrap)
        (iterate 1 nashPolarizationTrap)) ∧
    -- (1b) Each depolarization step is a Bule three-face optimal move
    BuleThreeFaceOptimalMove
        (threeFaceBule (iterate 0 nashPolarizationTrap))
        (threeFaceBule (iterate 1 nashPolarizationTrap)) ∧
    -- (1c) Each depolarization step advances toward the frontier
    coordinationStreams (iterate 0 nashPolarizationTrap)
        < coordinationStreams (iterate 1 nashPolarizationTrap) ∧
    -- (2) Conservation on the depolarization phase
    combinedLedger (iterate 0 nashPolarizationTrap)
        = combinedLedger (iterate 5 nashPolarizationTrap) ∧
    -- (3a) Welfare continues past depolarization
    IsJointWelfareImprovement (iterate 5 nashPolarizationTrap)
        (iterate 6 nashPolarizationTrap) ∧
    -- (3b) But depolarization does not
    ¬ IsDepolarizationStep (iterate 5 nashPolarizationTrap)
        (iterate 6 nashPolarizationTrap) ∧
    -- (3c) The 3-face Bule projection cannot see the welfare gain
    ¬ BuleThreeFaceOptimalMove
        (threeFaceBule (iterate 5 nashPolarizationTrap))
        (threeFaceBule (iterate 6 nashPolarizationTrap)) ∧
    -- (3d) But the 5-fold lift does
    buleFiveFoldValue (fiveFoldLift (iterate 5 nashPolarizationTrap))
        < buleFiveFoldValue (fiveFoldLift (iterate 6 nashPolarizationTrap)) := by
  refine ⟨step_zero_to_one_couples_depolarization_and_pareto,
          step_zero_to_one_is_bule_optimal,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact step_zero_to_one_is_frontier_progress
  · have h := combined_ledger_invariant_on_depolarization_phase
    exact h.1.trans h.2.2.2.2.2.symm
  · exact step_five_to_six_is_pareto_without_depolarization.2.1
  · exact step_five_to_six_is_pareto_without_depolarization.1
  · exact step_five_to_six_is_not_bule_optimal
  · exact five_fold_value_strictly_grows_at_post_depolarization_step

/-! ## Honesty note

The thesis "depolarization and Pareto-improvement are the same
dynamic" is proved here in the precise, kernel-bound form: on the
canonical six-step Nash → ULR path, every depolarization step is
also a Pareto step, with the conversion mediated exactly by the
3-face Bule curve and the American-Frontier encoding. The
combined-ledger conservation on the depolarization phase makes
the conversion *quantitative*, not just qualitative — one unit of
spent polarization equals one unit of gained welfare.

The two phenomena are *not* identical at the level of pointwise
state-space predicates. Pareto-improvement is the strictly larger
dynamic, and the welfare-completion step (5 → 6) is the witness:
welfare can grow without polarization decreasing, when the
positions are already met but debts still have headroom. The
3-face Bule cannot see this gain; the 5-fold lift recovers it via
the constructive-interference coordinate, which is exactly the
role that `Gnosis.BuleFiveFold` was introduced to play.

The general claim "any depolarizing dynamic Pareto-improves under
suitable convexity" requires stochastic-stability machinery that
this module does not provide; it is the next theorem in the chain
once `Gnosis.ErgodicConvergence` is in place.
-/

end DepolarizationIsParetoImprovement
