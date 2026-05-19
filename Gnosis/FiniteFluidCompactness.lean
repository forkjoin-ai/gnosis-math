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

theorem conserved_mesh_accepted_by_every_weak_probe
    (cells : List FluxCell)
    (hconserved : FiniteVolumeConservation cells)
    (probe : WeakFluxProbe)
    (depth : Nat) :
    weak_flux_refinement_signature.answer cells probe depth :=
  weak_flux_answer_of_conservation cells hconserved probe depth

theorem conserved_mesh_zero_for_every_weak_probe
    (cells : List FluxCell)
    (hconserved : FiniteVolumeConservation cells)
    (probe : WeakFluxProbe) :
    weakFluxResidual cells probe = 0 :=
  weak_flux_residual_zero_of_conservation cells hconserved probe

theorem conserved_mesh_zero_fluid_iff_every_fluid_observer_accepts
    (cells : List FluxCell)
    (hconserved : FiniteVolumeConservation cells) :
    fluidResidualTotal
        (fluidResidualOfFiniteVolumeConservation cells hconserved) = 0
      ↔ ∀ observer : FluidResidualObserver, ∀ depth : Nat,
        fluid_residual_refinement_signature.answer
          (fluidResidualOfFiniteVolumeConservation cells hconserved)
          observer depth := by
  constructor
  · intro _
    intro observer depth
    exact conserved_mesh_accepted_by_every_fluid_observer
      cells hconserved observer depth
  · intro _
    exact finite_conserved_mesh_promotes_to_zero_fluid_residual
      cells hconserved

theorem conserved_mesh_no_hidden_defect
    (cells : List FluxCell)
    (hconserved : FiniteVolumeConservation cells) :
    (∀ probe : WeakFluxProbe, weakFluxResidual cells probe = 0)
      ∧ (∀ probe : WeakFluxProbe, ∀ depth : Nat,
        weak_flux_refinement_signature.answer cells probe depth)
      ∧ (fluidResidualTotal
        (fluidResidualOfFiniteVolumeConservation cells hconserved) = 0)
      ∧ (∀ observer : FluidResidualObserver, ∀ depth : Nat,
        fluid_residual_refinement_signature.answer
          (fluidResidualOfFiniteVolumeConservation cells hconserved)
          observer depth) := by
  exact ⟨
    (fun probe => conserved_mesh_zero_for_every_weak_probe cells hconserved probe),
    (fun probe depth =>
      conserved_mesh_accepted_by_every_weak_probe cells hconserved probe depth),
    finite_conserved_mesh_promotes_to_zero_fluid_residual cells hconserved,
    (fun observer depth =>
      conserved_mesh_accepted_by_every_fluid_observer
        cells hconserved observer depth)⟩

theorem divergence_free_internal_mesh_no_hidden_defect
    (exterior : List FluxCell)
    (exchanges : List InternalExchange)
    (hexterior : DivergenceFreeMesh exterior) :
    (∀ probe : WeakFluxProbe,
      weakFluxResidual (exterior ++ internalExchangeCells exchanges) probe = 0)
      ∧ (∀ probe : WeakFluxProbe, ∀ depth : Nat,
        weak_flux_refinement_signature.answer
          (exterior ++ internalExchangeCells exchanges) probe depth)
      ∧ (∀ observer : FluidResidualObserver, ∀ depth : Nat,
        fluid_residual_refinement_signature.answer
          (fluidResidualOfFiniteVolumeConservation
            (exterior ++ internalExchangeCells exchanges)
            (finite_volume_conservation_append_divergence_free_internal
              exterior exchanges hexterior))
          observer depth) := by
  have hconserved :=
    finite_volume_conservation_append_divergence_free_internal
      exterior exchanges hexterior
  exact ⟨
    (fun probe =>
      conserved_mesh_zero_for_every_weak_probe
        (exterior ++ internalExchangeCells exchanges) hconserved probe),
    (fun probe depth =>
      conserved_mesh_accepted_by_every_weak_probe
        (exterior ++ internalExchangeCells exchanges) hconserved probe depth),
    (fun observer depth =>
      divergence_free_internal_mesh_accepted_by_every_fluid_observer
        exterior exchanges hexterior observer depth)⟩

theorem approximate_weak_residual_compactness
    (cells : List FluxCell)
    (probe : WeakFluxProbe)
    (budget wider : FluidResidualBudget)
    (hcovers : FluidResidualBudgetCovers budget wider)
    (hweak : weakFluxResidual cells probe ≤ fluidResidualBudgetTotal budget) :
    FluidResidualBounded
      (fluidResidualOfWeakFlux cells probe)
      (fluidResidualBudgetTotal wider) := by
  exact fluid_residual_bounded_of_covering_budget
    (fluidResidualOfWeakFlux cells probe)
    budget wider hcovers
    (finite_weak_residual_promotes_to_bounded_fluid_residual
      cells probe budget hweak)

theorem approximate_weak_residual_every_covering_observer_accepts
    (cells : List FluxCell)
    (probe : WeakFluxProbe)
    (budget wider : FluidResidualBudget)
    (hcovers : FluidResidualBudgetCovers budget wider)
    (hweak : weakFluxResidual cells probe ≤ fluidResidualBudgetTotal budget) :
    ∀ observer : FluidResidualObserver, ∀ depth : Nat,
      fluidResidualBudgetTotal wider ≤ observer.tolerance + depth →
        fluid_residual_refinement_signature.answer
          (fluidResidualOfWeakFlux cells probe)
          observer depth := by
  intro observer depth hbudget
  exact bounded_weak_residual_has_no_unobserved_fluid_defect
    cells probe budget wider observer depth hweak hcovers hbudget

theorem approximate_weak_residual_no_hidden_fluid_defect
    (cells : List FluxCell)
    (probe : WeakFluxProbe)
    (budget wider : FluidResidualBudget)
    (hcovers : FluidResidualBudgetCovers budget wider)
    (hweak : weakFluxResidual cells probe ≤ fluidResidualBudgetTotal budget) :
    FluidResidualBounded
      (fluidResidualOfWeakFlux cells probe)
      (fluidResidualBudgetTotal wider)
      ∧ ∀ observer : FluidResidualObserver, ∀ depth : Nat,
        fluidResidualBudgetTotal wider ≤ observer.tolerance + depth →
          fluid_residual_refinement_signature.answer
            (fluidResidualOfWeakFlux cells probe)
            observer depth := by
  exact ⟨
    approximate_weak_residual_compactness
      cells probe budget wider hcovers hweak,
    approximate_weak_residual_every_covering_observer_accepts
      cells probe budget wider hcovers hweak⟩

theorem approximate_weak_answer_no_hidden_fluid_defect
    (cells : List FluxCell)
    (probe : WeakFluxProbe)
    (observer : FluidResidualObserver)
    (depth : Nat)
    (hweak : weak_flux_refinement_signature.answer cells probe depth)
    (htolerance : probe.tolerance ≤ observer.tolerance) :
    fluid_residual_refinement_signature.answer
      (fluidResidualOfWeakFlux cells probe)
      observer depth :=
  finite_fluid_observer_compactness_of_weak_answer
    cells probe observer depth hweak htolerance

end Gnosis
