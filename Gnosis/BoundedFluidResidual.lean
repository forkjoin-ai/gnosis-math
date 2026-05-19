import Gnosis.WeakResidual

namespace Gnosis

/-!
# Bounded Fluid Residual

Navier-Stokes-like bounded residual observers over finite advection, diffusion, pressure, and forcing budgets.
-/

/-! ## Navier-Stokes-like bounded residual observers -/

structure BoundedFluidResidual where
  advection : Nat
  diffusion : Nat
  pressure : Nat
  forcing : Nat
  deriving Repr, DecidableEq

def zeroFluidResidual : BoundedFluidResidual :=
  { advection := 0, diffusion := 0, pressure := 0, forcing := 0 }

def fluidResidualTotal (state : BoundedFluidResidual) : Nat :=
  state.advection + state.diffusion + state.pressure + state.forcing

structure FluidResidualBudget where
  advection : Nat
  diffusion : Nat
  pressure : Nat
  forcing : Nat
  deriving Repr, DecidableEq

def fluidResidualBudgetTotal (budget : FluidResidualBudget) : Nat :=
  budget.advection + budget.diffusion + budget.pressure + budget.forcing

def FluidResidualBudgetCovers
    (budget wider : FluidResidualBudget) : Prop :=
  budget.advection ≤ wider.advection
    ∧ budget.diffusion ≤ wider.diffusion
    ∧ budget.pressure ≤ wider.pressure
    ∧ budget.forcing ≤ wider.forcing

theorem fluid_residual_budget_covers_refl
    (budget : FluidResidualBudget) :
    FluidResidualBudgetCovers budget budget := by
  exact ⟨Nat.le_refl budget.advection,
    Nat.le_refl budget.diffusion,
    Nat.le_refl budget.pressure,
    Nat.le_refl budget.forcing⟩

theorem fluid_residual_budget_covers_trans
    (left middle right : FluidResidualBudget)
    (hleftMiddle : FluidResidualBudgetCovers left middle)
    (hmiddleRight : FluidResidualBudgetCovers middle right) :
    FluidResidualBudgetCovers left right := by
  exact ⟨Nat.le_trans hleftMiddle.1 hmiddleRight.1,
    Nat.le_trans hleftMiddle.2.1 hmiddleRight.2.1,
    Nat.le_trans hleftMiddle.2.2.1 hmiddleRight.2.2.1,
    Nat.le_trans hleftMiddle.2.2.2 hmiddleRight.2.2.2⟩

structure FluidResidualObserver where
  tolerance : Nat
  deriving Repr, DecidableEq

def fluidResidualAnswer
    (state : BoundedFluidResidual)
    (observer : FluidResidualObserver)
    (depth : Nat) : Prop :=
  fluidResidualTotal state ≤ observer.tolerance + depth

def fluid_residual_refinement_signature :
    RefinementSignature BoundedFluidResidual FluidResidualObserver :=
  { answer := fluidResidualAnswer }

def FluidResidualBounded
    (state : BoundedFluidResidual)
    (budget : Nat) : Prop :=
  fluidResidualTotal state ≤ budget

theorem fluid_residual_total_le_sum_budget
    (state : BoundedFluidResidual)
    (advectionBudget diffusionBudget pressureBudget forcingBudget : Nat)
    (hadvection : state.advection ≤ advectionBudget)
    (hdiffusion : state.diffusion ≤ diffusionBudget)
    (hpressure : state.pressure ≤ pressureBudget)
    (hforcing : state.forcing ≤ forcingBudget) :
    fluidResidualTotal state ≤
      advectionBudget + diffusionBudget + pressureBudget + forcingBudget := by
  unfold fluidResidualTotal
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add hadvection hdiffusion) hpressure)
    hforcing

theorem fluid_residual_bounded_of_component_budgets
    (state : BoundedFluidResidual)
    (advectionBudget diffusionBudget pressureBudget forcingBudget : Nat)
    (hadvection : state.advection ≤ advectionBudget)
    (hdiffusion : state.diffusion ≤ diffusionBudget)
    (hpressure : state.pressure ≤ pressureBudget)
    (hforcing : state.forcing ≤ forcingBudget) :
    FluidResidualBounded state
      (advectionBudget + diffusionBudget + pressureBudget + forcingBudget) :=
  fluid_residual_total_le_sum_budget state
    advectionBudget diffusionBudget pressureBudget forcingBudget
    hadvection hdiffusion hpressure hforcing

theorem fluid_residual_total_le_budget
    (state : BoundedFluidResidual)
    (budget : FluidResidualBudget)
    (hadvection : state.advection ≤ budget.advection)
    (hdiffusion : state.diffusion ≤ budget.diffusion)
    (hpressure : state.pressure ≤ budget.pressure)
    (hforcing : state.forcing ≤ budget.forcing) :
    fluidResidualTotal state ≤ fluidResidualBudgetTotal budget := by
  exact fluid_residual_total_le_sum_budget state
    budget.advection budget.diffusion budget.pressure budget.forcing
    hadvection hdiffusion hpressure hforcing

theorem fluid_residual_bounded_of_budget
    (state : BoundedFluidResidual)
    (budget : FluidResidualBudget)
    (hadvection : state.advection ≤ budget.advection)
    (hdiffusion : state.diffusion ≤ budget.diffusion)
    (hpressure : state.pressure ≤ budget.pressure)
    (hforcing : state.forcing ≤ budget.forcing) :
    FluidResidualBounded state (fluidResidualBudgetTotal budget) :=
  fluid_residual_total_le_budget state budget
    hadvection hdiffusion hpressure hforcing

theorem fluid_residual_answer_of_budget_le
    (state : BoundedFluidResidual)
    (observer : FluidResidualObserver)
    (depth budget : Nat)
    (hbounded : FluidResidualBounded state budget)
    (hbudget : budget ≤ observer.tolerance + depth) :
    fluid_residual_refinement_signature.answer state observer depth := by
  change fluidResidualTotal state ≤ observer.tolerance + depth
  exact Nat.le_trans hbounded hbudget

theorem fluid_residual_answer_of_total_le_tolerance
    (state : BoundedFluidResidual)
    (observer : FluidResidualObserver)
    (depth : Nat)
    (htotal : fluidResidualTotal state ≤ observer.tolerance) :
    fluid_residual_refinement_signature.answer state observer depth := by
  change fluidResidualTotal state ≤ observer.tolerance + depth
  exact Nat.le_trans htotal (Nat.le_add_right observer.tolerance depth)

theorem zero_fluid_residual_answer
    (observer : FluidResidualObserver)
    (depth : Nat) :
    fluid_residual_refinement_signature.answer
      zeroFluidResidual
      observer depth := by
  change 0 + 0 + 0 + 0 ≤ observer.tolerance + depth
  simp

theorem zero_fluid_residual_total :
    fluidResidualTotal zeroFluidResidual = 0 := by
  rfl

theorem zero_fluid_residual_bounded (budget : Nat) :
    FluidResidualBounded zeroFluidResidual budget := by
  unfold FluidResidualBounded
  rw [zero_fluid_residual_total]
  exact Nat.zero_le budget

theorem fluid_residual_refinement_complete
    (state : BoundedFluidResidual) :
    RefinementComplete fluid_residual_refinement_signature state := by
  intro observer
  refine ⟨fluidResidualTotal state, ?_⟩
  intro extra
  change fluidResidualTotal state ≤
    observer.tolerance + (fluidResidualTotal state + extra)
  have hassoc : observer.tolerance + fluidResidualTotal state + extra =
      observer.tolerance + (fluidResidualTotal state + extra) :=
    Nat.add_assoc observer.tolerance (fluidResidualTotal state) extra
  rw [← hassoc]
  exact Nat.le_trans
    (Nat.le_add_left (fluidResidualTotal state) observer.tolerance)
    (Nat.le_add_right
      (observer.tolerance + fluidResidualTotal state) extra)

theorem fluid_residual_refinement_tail_equal
    (left right : BoundedFluidResidual) :
    RefinementTailEqual fluid_residual_refinement_signature left right := by
  intro observer
  refine ⟨fluidResidualTotal left + fluidResidualTotal right, ?_⟩
  intro extra
  unfold fluid_residual_refinement_signature fluidResidualAnswer
  have hleft : fluidResidualTotal left ≤
      observer.tolerance +
        (fluidResidualTotal left + fluidResidualTotal right + extra) := by
    rw [Nat.add_assoc (fluidResidualTotal left) (fluidResidualTotal right) extra]
    exact Nat.le_trans
      (Nat.le_add_right (fluidResidualTotal left)
        (fluidResidualTotal right + extra))
      (Nat.le_add_left
        (fluidResidualTotal left + (fluidResidualTotal right + extra))
        observer.tolerance)
  have hright : fluidResidualTotal right ≤
      observer.tolerance +
        (fluidResidualTotal left + fluidResidualTotal right + extra) := by
    have hbase : fluidResidualTotal right ≤
        fluidResidualTotal left + fluidResidualTotal right + extra := by
      exact Nat.le_trans
        (Nat.le_add_left (fluidResidualTotal right) (fluidResidualTotal left))
        (Nat.le_add_right
          (fluidResidualTotal left + fluidResidualTotal right) extra)
    exact Nat.le_trans hbase
      (Nat.le_add_left
        (fluidResidualTotal left + fluidResidualTotal right + extra)
        observer.tolerance)
  exact ⟨fun _ => hright, fun _ => hleft⟩

def fluidResidualOfFiniteVolumeConservation
    (_cells : List FluxCell)
    (_hconserved : FiniteVolumeConservation _cells) :
    BoundedFluidResidual :=
  zeroFluidResidual

theorem fluid_residual_of_conservation_zero
    (cells : List FluxCell)
    (hconserved : FiniteVolumeConservation cells) :
    fluidResidualTotal
        (fluidResidualOfFiniteVolumeConservation cells hconserved) = 0 := by
  rfl

theorem fluid_residual_answer_of_conservation
    (cells : List FluxCell)
    (hconserved : FiniteVolumeConservation cells)
    (observer : FluidResidualObserver)
    (depth : Nat) :
    fluid_residual_refinement_signature.answer
      (fluidResidualOfFiniteVolumeConservation cells hconserved)
      observer depth := by
  exact zero_fluid_residual_answer observer depth

theorem fluid_residual_answer_of_divergence_free_internal
    (exterior : List FluxCell)
    (exchanges : List InternalExchange)
    (hexterior : DivergenceFreeMesh exterior)
    (observer : FluidResidualObserver)
    (depth : Nat) :
    fluid_residual_refinement_signature.answer
      (fluidResidualOfFiniteVolumeConservation
        (exterior ++ internalExchangeCells exchanges)
        (finite_volume_conservation_append_divergence_free_internal
          exterior exchanges hexterior))
      observer depth := by
  exact zero_fluid_residual_answer observer depth

def fluidResidualOfWeakFlux
    (cells : List FluxCell)
    (probe : WeakFluxProbe) :
    BoundedFluidResidual :=
  { advection := weakFluxResidual cells probe,
    diffusion := 0,
    pressure := 0,
    forcing := 0 }

theorem fluid_residual_of_weak_flux_total
    (cells : List FluxCell)
    (probe : WeakFluxProbe) :
    fluidResidualTotal (fluidResidualOfWeakFlux cells probe) =
      weakFluxResidual cells probe := by
  unfold fluidResidualOfWeakFlux fluidResidualTotal
  simp

theorem fluid_residual_of_weak_flux_bounded
    (cells : List FluxCell)
    (probe : WeakFluxProbe)
    (budget : Nat)
    (hweak : weakFluxResidual cells probe ≤ budget) :
    FluidResidualBounded (fluidResidualOfWeakFlux cells probe) budget := by
  unfold FluidResidualBounded
  rw [fluid_residual_of_weak_flux_total]
  exact hweak

theorem fluid_residual_answer_of_weak_flux_bound
    (cells : List FluxCell)
    (probe : WeakFluxProbe)
    (observer : FluidResidualObserver)
    (depth budget : Nat)
    (hweak : weakFluxResidual cells probe ≤ budget)
    (hbudget : budget ≤ observer.tolerance + depth) :
    fluid_residual_refinement_signature.answer
      (fluidResidualOfWeakFlux cells probe)
      observer depth := by
  apply fluid_residual_answer_of_budget_le
  · exact fluid_residual_of_weak_flux_bounded cells probe budget hweak
  · exact hbudget

theorem fluid_residual_answer_of_weak_flux_answer
    (cells : List FluxCell)
    (probe : WeakFluxProbe)
    (observer : FluidResidualObserver)
    (depth : Nat)
    (hweak : weak_flux_refinement_signature.answer cells probe depth)
    (htolerance : probe.tolerance ≤ observer.tolerance) :
    fluid_residual_refinement_signature.answer
      (fluidResidualOfWeakFlux cells probe)
      observer depth := by
  change weakFluxResidual cells probe ≤ probe.tolerance + depth at hweak
  change fluidResidualTotal (fluidResidualOfWeakFlux cells probe) ≤
    observer.tolerance + depth
  rw [fluid_residual_of_weak_flux_total]
  exact Nat.le_trans hweak
    (Nat.add_le_add_right htolerance depth)

theorem fluid_residual_answer_mono_tolerance
    (state : BoundedFluidResidual)
    (observer wider : FluidResidualObserver)
    (depth : Nat)
    (htolerance : observer.tolerance ≤ wider.tolerance)
    (hanswer :
      fluid_residual_refinement_signature.answer state observer depth) :
    fluid_residual_refinement_signature.answer state wider depth := by
  change fluidResidualTotal state ≤ observer.tolerance + depth at hanswer
  change fluidResidualTotal state ≤ wider.tolerance + depth
  exact Nat.le_trans hanswer (Nat.add_le_add_right htolerance depth)

theorem fluid_residual_answer_mono_tolerance_value
    (state : BoundedFluidResidual)
    (tolerance widerTolerance depth : Nat)
    (htolerance : tolerance ≤ widerTolerance)
    (hanswer :
      fluid_residual_refinement_signature.answer state
        { tolerance := tolerance } depth) :
    fluid_residual_refinement_signature.answer state
      { tolerance := widerTolerance } depth := by
  exact fluid_residual_answer_mono_tolerance state
    { tolerance := tolerance } { tolerance := widerTolerance }
    depth htolerance hanswer

theorem fluid_residual_answer_of_weak_flux_answer_wider
    (cells : List FluxCell)
    (probe : WeakFluxProbe)
    (observer wider : FluidResidualObserver)
    (depth : Nat)
    (hweak : weak_flux_refinement_signature.answer cells probe depth)
    (hprobeObserver : probe.tolerance ≤ observer.tolerance)
    (hobserverWider : observer.tolerance ≤ wider.tolerance) :
    fluid_residual_refinement_signature.answer
      (fluidResidualOfWeakFlux cells probe)
      wider depth := by
  apply fluid_residual_answer_mono_tolerance
    (fluidResidualOfWeakFlux cells probe) observer wider depth hobserverWider
  exact fluid_residual_answer_of_weak_flux_answer
    cells probe observer depth hweak hprobeObserver

theorem fluid_residual_total_mono_components
    (lower upper : BoundedFluidResidual)
    (hadvection : lower.advection ≤ upper.advection)
    (hdiffusion : lower.diffusion ≤ upper.diffusion)
    (hpressure : lower.pressure ≤ upper.pressure)
    (hforcing : lower.forcing ≤ upper.forcing) :
    fluidResidualTotal lower ≤ fluidResidualTotal upper := by
  unfold fluidResidualTotal
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add hadvection hdiffusion) hpressure)
    hforcing

theorem fluid_residual_bounded_of_componentwise_le
    (lower upper : BoundedFluidResidual)
    (budget : Nat)
    (hadvection : lower.advection ≤ upper.advection)
    (hdiffusion : lower.diffusion ≤ upper.diffusion)
    (hpressure : lower.pressure ≤ upper.pressure)
    (hforcing : lower.forcing ≤ upper.forcing)
    (hupper : FluidResidualBounded upper budget) :
    FluidResidualBounded lower budget := by
  unfold FluidResidualBounded at hupper ⊢
  exact Nat.le_trans
    (fluid_residual_total_mono_components lower upper
      hadvection hdiffusion hpressure hforcing)
    hupper

theorem fluid_residual_answer_of_componentwise_le
    (lower upper : BoundedFluidResidual)
    (observer : FluidResidualObserver)
    (depth : Nat)
    (hadvection : lower.advection ≤ upper.advection)
    (hdiffusion : lower.diffusion ≤ upper.diffusion)
    (hpressure : lower.pressure ≤ upper.pressure)
    (hforcing : lower.forcing ≤ upper.forcing)
    (hupper :
      fluid_residual_refinement_signature.answer upper observer depth) :
    fluid_residual_refinement_signature.answer lower observer depth := by
  change fluidResidualTotal upper ≤ observer.tolerance + depth at hupper
  change fluidResidualTotal lower ≤ observer.tolerance + depth
  exact Nat.le_trans
    (fluid_residual_total_mono_components lower upper
      hadvection hdiffusion hpressure hforcing)
    hupper

theorem fluid_residual_sum_budget_mono
    (advectionBudget diffusionBudget pressureBudget forcingBudget : Nat)
    (widerAdvection widerDiffusion widerPressure widerForcing : Nat)
    (hadvection : advectionBudget ≤ widerAdvection)
    (hdiffusion : diffusionBudget ≤ widerDiffusion)
    (hpressure : pressureBudget ≤ widerPressure)
    (hforcing : forcingBudget ≤ widerForcing) :
    advectionBudget + diffusionBudget + pressureBudget + forcingBudget ≤
      widerAdvection + widerDiffusion + widerPressure + widerForcing := by
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add hadvection hdiffusion) hpressure)
    hforcing

theorem fluid_residual_bounded_of_wider_component_budgets
    (state : BoundedFluidResidual)
    (advectionBudget diffusionBudget pressureBudget forcingBudget : Nat)
    (widerAdvection widerDiffusion widerPressure widerForcing : Nat)
    (hadvection : advectionBudget ≤ widerAdvection)
    (hdiffusion : diffusionBudget ≤ widerDiffusion)
    (hpressure : pressureBudget ≤ widerPressure)
    (hforcing : forcingBudget ≤ widerForcing)
    (hbounded :
      FluidResidualBounded state
        (advectionBudget + diffusionBudget + pressureBudget + forcingBudget)) :
    FluidResidualBounded state
      (widerAdvection + widerDiffusion + widerPressure + widerForcing) := by
  unfold FluidResidualBounded at hbounded ⊢
  exact Nat.le_trans hbounded
    (fluid_residual_sum_budget_mono
      advectionBudget diffusionBudget pressureBudget forcingBudget
      widerAdvection widerDiffusion widerPressure widerForcing
      hadvection hdiffusion hpressure hforcing)

theorem fluid_residual_answer_of_wider_component_budgets
    (state : BoundedFluidResidual)
    (observer : FluidResidualObserver)
    (depth : Nat)
    (advectionBudget diffusionBudget pressureBudget forcingBudget : Nat)
    (widerAdvection widerDiffusion widerPressure widerForcing : Nat)
    (hadvection : advectionBudget ≤ widerAdvection)
    (hdiffusion : diffusionBudget ≤ widerDiffusion)
    (hpressure : pressureBudget ≤ widerPressure)
    (hforcing : forcingBudget ≤ widerForcing)
    (hbounded :
      FluidResidualBounded state
        (advectionBudget + diffusionBudget + pressureBudget + forcingBudget))
    (hbudget :
      widerAdvection + widerDiffusion + widerPressure + widerForcing ≤
        observer.tolerance + depth) :
    fluid_residual_refinement_signature.answer state observer depth := by
  exact fluid_residual_answer_of_budget_le state observer depth
    (widerAdvection + widerDiffusion + widerPressure + widerForcing)
    (fluid_residual_bounded_of_wider_component_budgets state
      advectionBudget diffusionBudget pressureBudget forcingBudget
      widerAdvection widerDiffusion widerPressure widerForcing
      hadvection hdiffusion hpressure hforcing hbounded)
    hbudget

theorem fluid_residual_budget_total_mono
    (budget wider : FluidResidualBudget)
    (hadvection : budget.advection ≤ wider.advection)
    (hdiffusion : budget.diffusion ≤ wider.diffusion)
    (hpressure : budget.pressure ≤ wider.pressure)
    (hforcing : budget.forcing ≤ wider.forcing) :
    fluidResidualBudgetTotal budget ≤ fluidResidualBudgetTotal wider := by
  exact fluid_residual_sum_budget_mono
    budget.advection budget.diffusion budget.pressure budget.forcing
    wider.advection wider.diffusion wider.pressure wider.forcing
    hadvection hdiffusion hpressure hforcing

theorem fluid_residual_budget_total_mono_of_covers
    (budget wider : FluidResidualBudget)
    (hcovers : FluidResidualBudgetCovers budget wider) :
    fluidResidualBudgetTotal budget ≤ fluidResidualBudgetTotal wider :=
  fluid_residual_budget_total_mono budget wider
    hcovers.1 hcovers.2.1 hcovers.2.2.1 hcovers.2.2.2

theorem fluid_residual_bounded_of_wider_budget
    (state : BoundedFluidResidual)
    (budget wider : FluidResidualBudget)
    (hadvection : budget.advection ≤ wider.advection)
    (hdiffusion : budget.diffusion ≤ wider.diffusion)
    (hpressure : budget.pressure ≤ wider.pressure)
    (hforcing : budget.forcing ≤ wider.forcing)
    (hbounded : FluidResidualBounded state (fluidResidualBudgetTotal budget)) :
    FluidResidualBounded state (fluidResidualBudgetTotal wider) := by
  unfold FluidResidualBounded at hbounded ⊢
  exact Nat.le_trans hbounded
    (fluid_residual_budget_total_mono budget wider
      hadvection hdiffusion hpressure hforcing)

theorem fluid_residual_bounded_of_covering_budget
    (state : BoundedFluidResidual)
    (budget wider : FluidResidualBudget)
    (hcovers : FluidResidualBudgetCovers budget wider)
    (hbounded : FluidResidualBounded state (fluidResidualBudgetTotal budget)) :
    FluidResidualBounded state (fluidResidualBudgetTotal wider) := by
  unfold FluidResidualBounded at hbounded ⊢
  exact Nat.le_trans hbounded
    (fluid_residual_budget_total_mono_of_covers budget wider hcovers)

theorem fluid_residual_answer_of_budget
    (state : BoundedFluidResidual)
    (budget : FluidResidualBudget)
    (observer : FluidResidualObserver)
    (depth : Nat)
    (hadvection : state.advection ≤ budget.advection)
    (hdiffusion : state.diffusion ≤ budget.diffusion)
    (hpressure : state.pressure ≤ budget.pressure)
    (hforcing : state.forcing ≤ budget.forcing)
    (hbudget : fluidResidualBudgetTotal budget ≤ observer.tolerance + depth) :
    fluid_residual_refinement_signature.answer state observer depth := by
  exact fluid_residual_answer_of_budget_le state observer depth
    (fluidResidualBudgetTotal budget)
    (fluid_residual_bounded_of_budget state budget
      hadvection hdiffusion hpressure hforcing)
    hbudget

theorem fluid_residual_answer_of_wider_budget
    (state : BoundedFluidResidual)
    (budget wider : FluidResidualBudget)
    (observer : FluidResidualObserver)
    (depth : Nat)
    (hadvection : budget.advection ≤ wider.advection)
    (hdiffusion : budget.diffusion ≤ wider.diffusion)
    (hpressure : budget.pressure ≤ wider.pressure)
    (hforcing : budget.forcing ≤ wider.forcing)
    (hbounded : FluidResidualBounded state (fluidResidualBudgetTotal budget))
    (hbudget : fluidResidualBudgetTotal wider ≤ observer.tolerance + depth) :
    fluid_residual_refinement_signature.answer state observer depth := by
  exact fluid_residual_answer_of_budget_le state observer depth
    (fluidResidualBudgetTotal wider)
    (fluid_residual_bounded_of_wider_budget state budget wider
      hadvection hdiffusion hpressure hforcing hbounded)
    hbudget

theorem fluid_residual_answer_of_covering_budget
    (state : BoundedFluidResidual)
    (budget wider : FluidResidualBudget)
    (observer : FluidResidualObserver)
    (depth : Nat)
    (hcovers : FluidResidualBudgetCovers budget wider)
    (hbounded : FluidResidualBounded state (fluidResidualBudgetTotal budget))
    (hbudget : fluidResidualBudgetTotal wider ≤ observer.tolerance + depth) :
    fluid_residual_refinement_signature.answer state observer depth := by
  exact fluid_residual_answer_of_budget_le state observer depth
    (fluidResidualBudgetTotal wider)
    (fluid_residual_bounded_of_covering_budget state budget wider hcovers hbounded)
    hbudget

end Gnosis
