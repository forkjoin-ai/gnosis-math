import Gnosis.WeakResidual
import Gnosis.BoundedFluidResidual

namespace Gnosis

/-!
# Finite Fluid Compactness

Observer-compact finite fluid pipeline: finite-volume conservation and weak
residual acceptance promote into bounded fluid residual observer acceptance
without introducing continuous operators.
-/

theorem finite_conserved_mesh_promotes_to_zero_fluid_residual
    (cells : List FluxCell)
    (hconserved : FiniteVolumeConservation cells) :
    fluidResidualTotal
      (fluidResidualOfFiniteVolumeConservation cells hconserved) = 0 :=
  fluid_residual_of_conservation_zero cells hconserved

theorem conserved_mesh_accepted_by_every_fluid_observer
    (cells : List FluxCell)
    (hconserved : FiniteVolumeConservation cells)
    (observer : FluidResidualObserver)
    (depth : Nat) :
    fluid_residual_refinement_signature.answer
      (fluidResidualOfFiniteVolumeConservation cells hconserved)
      observer depth :=
  fluid_residual_answer_of_conservation cells hconserved observer depth

theorem divergence_free_internal_mesh_has_no_fluid_residual_shadow
    (exterior : List FluxCell)
    (exchanges : List InternalExchange)
    (hexterior : DivergenceFreeMesh exterior) :
    fluidResidualTotal
      (fluidResidualOfFiniteVolumeConservation
        (exterior ++ internalExchangeCells exchanges)
        (finite_volume_conservation_append_divergence_free_internal
          exterior exchanges hexterior)) = 0 := by
  exact fluid_residual_of_conservation_zero
    (exterior ++ internalExchangeCells exchanges)
    (finite_volume_conservation_append_divergence_free_internal
      exterior exchanges hexterior)

theorem divergence_free_internal_mesh_accepted_by_every_fluid_observer
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
      observer depth :=
  fluid_residual_answer_of_divergence_free_internal
    exterior exchanges hexterior observer depth

theorem finite_weak_residual_promotes_to_bounded_fluid_residual
    (cells : List FluxCell)
    (probe : WeakFluxProbe)
    (budget : FluidResidualBudget)
    (hbudget : weakFluxResidual cells probe ≤ fluidResidualBudgetTotal budget) :
    FluidResidualBounded
      (fluidResidualOfWeakFlux cells probe)
      (fluidResidualBudgetTotal budget) :=
  fluid_residual_of_weak_flux_bounded
    cells probe (fluidResidualBudgetTotal budget) hbudget

theorem finite_fluid_observer_compactness
    (cells : List FluxCell)
    (probe : WeakFluxProbe)
    (budget : FluidResidualBudget)
    (observer : FluidResidualObserver)
    (depth : Nat)
    (hweak : weakFluxResidual cells probe ≤ fluidResidualBudgetTotal budget)
    (hbudget : fluidResidualBudgetTotal budget ≤ observer.tolerance + depth) :
    fluid_residual_refinement_signature.answer
      (fluidResidualOfWeakFlux cells probe)
      observer depth := by
  exact fluid_residual_answer_of_budget_le
    (fluidResidualOfWeakFlux cells probe)
    observer depth
    (fluidResidualBudgetTotal budget)
    (finite_weak_residual_promotes_to_bounded_fluid_residual
      cells probe budget hweak)
    hbudget

theorem finite_fluid_observer_compactness_of_weak_answer
    (cells : List FluxCell)
    (probe : WeakFluxProbe)
    (observer : FluidResidualObserver)
    (depth : Nat)
    (hweak : weak_flux_refinement_signature.answer cells probe depth)
    (htolerance : probe.tolerance ≤ observer.tolerance) :
    fluid_residual_refinement_signature.answer
      (fluidResidualOfWeakFlux cells probe)
      observer depth :=
  fluid_residual_answer_of_weak_flux_answer
    cells probe observer depth hweak htolerance

theorem bounded_weak_residual_has_no_unobserved_fluid_defect
    (cells : List FluxCell)
    (probe : WeakFluxProbe)
    (budget wider : FluidResidualBudget)
    (observer : FluidResidualObserver)
    (depth : Nat)
    (hweak : weakFluxResidual cells probe ≤ fluidResidualBudgetTotal budget)
    (hcovers : FluidResidualBudgetCovers budget wider)
    (hbudget : fluidResidualBudgetTotal wider ≤ observer.tolerance + depth) :
    fluid_residual_refinement_signature.answer
      (fluidResidualOfWeakFlux cells probe)
      observer depth := by
  exact fluid_residual_answer_of_covering_budget
    (fluidResidualOfWeakFlux cells probe)
    budget wider observer depth
    hcovers
    (finite_weak_residual_promotes_to_bounded_fluid_residual
      cells probe budget hweak)
    hbudget

end Gnosis
