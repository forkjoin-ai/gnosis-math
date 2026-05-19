import Gnosis.BoundedFluidResidual
import Gnosis.FiniteProbabilityCore.CalculusExporters

namespace Gnosis
namespace FiniteCalculusProbability

/-!
# Finite Calculus Probability

Export finite-volume, weak-residual, and bounded-fluid residual witnesses as
native finite probability processes. The probability channel records conserved
input/output mass; the calculus residual records the observable shadow left by
finite approximation, weak probing, or fluid-budget imbalance.
-/

def finiteVolumeResidualShadow (cells : List FluxCell) : Nat :=
  finiteVolumeResidual cells + finiteVolumeDeficit cells

def finiteVolumeProcess
    (channel : FiniteProbabilityCore.FiniteProbabilityChannel)
    (cells : List FluxCell) :
    FiniteProbabilityCore.FiniteProbabilityProcess :=
  FiniteProbabilityCore.processOfResidual channel
    (finiteVolumeResidualShadow cells)

theorem finite_volume_process_residual_eq
    (channel : FiniteProbabilityCore.FiniteProbabilityChannel)
    (cells : List FluxCell) :
    (finiteVolumeProcess channel cells).residual =
      channel.lostMass + finiteVolumeResidualShadow cells := rfl

theorem finite_volume_process_residual_eq_lost_of_conservation
    (channel : FiniteProbabilityCore.FiniteProbabilityChannel)
    (cells : List FluxCell)
    (hconserved : FiniteVolumeConservation cells) :
    (finiteVolumeProcess channel cells).residual = channel.lostMass := by
  unfold finiteVolumeProcess finiteVolumeResidualShadow
  rw [hconserved.balanced.1, hconserved.balanced.2]
  simp [FiniteProbabilityCore.processOfResidual]

theorem finite_volume_process_no_hidden_defect_of_conservation
    (channel : FiniteProbabilityCore.FiniteProbabilityChannel)
    (cells : List FluxCell)
    (hconserved : FiniteVolumeConservation cells)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hresidual : channel.lostMass ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (FiniteProbabilityCore.probabilityObserverPromotion.promote
        (finiteVolumeProcess channel cells).residualState ())
      observer depth := by
  apply FiniteProbabilityCore.process_no_hidden_defect
  · rwa [finite_volume_process_residual_eq_lost_of_conservation
      channel cells hconserved]
  · exact hcovers
  · exact hbudget

def transportResidualShadow (region : TransportRegion) : Nat :=
  transportResidual region + transportDeficit region

def transportRegionProcess
    (channel : FiniteProbabilityCore.FiniteProbabilityChannel)
    (region : TransportRegion) :
    FiniteProbabilityCore.FiniteProbabilityProcess :=
  FiniteProbabilityCore.processOfResidual channel
    (transportResidualShadow region)

theorem transport_region_process_residual_eq
    (channel : FiniteProbabilityCore.FiniteProbabilityChannel)
    (region : TransportRegion) :
    (transportRegionProcess channel region).residual =
      channel.lostMass + transportResidualShadow region := rfl

theorem transport_region_process_residual_eq_lost_of_exact
    (channel : FiniteProbabilityCore.FiniteProbabilityChannel)
    (region : TransportRegion)
    (hexact : TransportExact region) :
    (transportRegionProcess channel region).residual =
      channel.lostMass := by
  unfold transportRegionProcess transportResidualShadow
  rw [transport_exact_residual_zero region hexact,
    transport_exact_deficit_zero region hexact]
  simp [FiniteProbabilityCore.processOfResidual]

theorem transport_region_process_no_hidden_defect_of_exact
    (channel : FiniteProbabilityCore.FiniteProbabilityChannel)
    (region : TransportRegion)
    (hexact : TransportExact region)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hresidual : channel.lostMass ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (FiniteProbabilityCore.probabilityObserverPromotion.promote
        (transportRegionProcess channel region).residualState ())
      observer depth := by
  apply FiniteProbabilityCore.process_no_hidden_defect
  · rwa [transport_region_process_residual_eq_lost_of_exact
      channel region hexact]
  · exact hcovers
  · exact hbudget

def weakFluxProcess
    (channel : FiniteProbabilityCore.FiniteProbabilityChannel)
    (cells : List FluxCell)
    (probe : WeakFluxProbe) :
    FiniteProbabilityCore.FiniteProbabilityProcess :=
  FiniteProbabilityCore.processOfResidual channel
    (weakFluxResidual cells probe)

theorem weak_flux_process_residual_eq
    (channel : FiniteProbabilityCore.FiniteProbabilityChannel)
    (cells : List FluxCell)
    (probe : WeakFluxProbe) :
    (weakFluxProcess channel cells probe).residual =
      channel.lostMass + weakFluxResidual cells probe := rfl

theorem weak_flux_process_residual_eq_lost_of_conservation
    (channel : FiniteProbabilityCore.FiniteProbabilityChannel)
    (cells : List FluxCell)
    (hconserved : FiniteVolumeConservation cells)
    (probe : WeakFluxProbe) :
    (weakFluxProcess channel cells probe).residual = channel.lostMass := by
  unfold weakFluxProcess
  rw [weak_flux_residual_zero_of_conservation cells hconserved probe]
  simp [FiniteProbabilityCore.processOfResidual]

theorem weak_flux_process_no_hidden_defect_of_conservation
    (channel : FiniteProbabilityCore.FiniteProbabilityChannel)
    (cells : List FluxCell)
    (hconserved : FiniteVolumeConservation cells)
    (probe : WeakFluxProbe)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hresidual : channel.lostMass ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (FiniteProbabilityCore.probabilityObserverPromotion.promote
        (weakFluxProcess channel cells probe).residualState ())
      observer depth := by
  apply FiniteProbabilityCore.process_no_hidden_defect
  · rwa [weak_flux_process_residual_eq_lost_of_conservation
      channel cells hconserved probe]
  · exact hcovers
  · exact hbudget

def boundedFluidProcess
    (channel : FiniteProbabilityCore.FiniteProbabilityChannel)
    (state : BoundedFluidResidual) :
    FiniteProbabilityCore.FiniteProbabilityProcess :=
  FiniteProbabilityCore.processOfResidual channel
    (fluidResidualTotal state)

theorem bounded_fluid_process_residual_eq
    (channel : FiniteProbabilityCore.FiniteProbabilityChannel)
    (state : BoundedFluidResidual) :
    (boundedFluidProcess channel state).residual =
      channel.lostMass + fluidResidualTotal state := rfl

theorem zero_bounded_fluid_process_residual_eq_lost
    (channel : FiniteProbabilityCore.FiniteProbabilityChannel) :
    (boundedFluidProcess channel zeroFluidResidual).residual =
      channel.lostMass := by
  unfold boundedFluidProcess
  rw [zero_fluid_residual_total]
  simp [FiniteProbabilityCore.processOfResidual]

theorem zero_bounded_fluid_process_no_hidden_defect
    (channel : FiniteProbabilityCore.FiniteProbabilityChannel)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hresidual : channel.lostMass ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (FiniteProbabilityCore.probabilityObserverPromotion.promote
        (boundedFluidProcess channel zeroFluidResidual).residualState ())
      observer depth := by
  apply FiniteProbabilityCore.process_no_hidden_defect
  · rwa [zero_bounded_fluid_process_residual_eq_lost]
  · exact hcovers
  · exact hbudget

def conservationFluidProcess
    (channel : FiniteProbabilityCore.FiniteProbabilityChannel)
    (cells : List FluxCell)
    (hconserved : FiniteVolumeConservation cells) :
    FiniteProbabilityCore.FiniteProbabilityProcess :=
  boundedFluidProcess channel
    (fluidResidualOfFiniteVolumeConservation cells hconserved)

theorem conservation_fluid_process_residual_eq_lost
    (channel : FiniteProbabilityCore.FiniteProbabilityChannel)
    (cells : List FluxCell)
    (hconserved : FiniteVolumeConservation cells) :
    (conservationFluidProcess channel cells hconserved).residual =
      channel.lostMass := by
  unfold conservationFluidProcess boundedFluidProcess
  rw [fluid_residual_of_conservation_zero cells hconserved]
  simp [FiniteProbabilityCore.processOfResidual]

theorem conservation_fluid_process_no_hidden_defect
    (channel : FiniteProbabilityCore.FiniteProbabilityChannel)
    (cells : List FluxCell)
    (hconserved : FiniteVolumeConservation cells)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hresidual : channel.lostMass ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (FiniteProbabilityCore.probabilityObserverPromotion.promote
        (conservationFluidProcess channel cells hconserved).residualState ())
      observer depth := by
  apply FiniteProbabilityCore.process_no_hidden_defect
  · rwa [conservation_fluid_process_residual_eq_lost]
  · exact hcovers
  · exact hbudget

def weakFluxFluidProcess
    (channel : FiniteProbabilityCore.FiniteProbabilityChannel)
    (cells : List FluxCell)
    (probe : WeakFluxProbe) :
    FiniteProbabilityCore.FiniteProbabilityProcess :=
  boundedFluidProcess channel (fluidResidualOfWeakFlux cells probe)

theorem weak_flux_fluid_process_residual_eq
    (channel : FiniteProbabilityCore.FiniteProbabilityChannel)
    (cells : List FluxCell)
    (probe : WeakFluxProbe) :
    (weakFluxFluidProcess channel cells probe).residual =
      channel.lostMass + weakFluxResidual cells probe := by
  unfold weakFluxFluidProcess boundedFluidProcess
  rw [fluid_residual_of_weak_flux_total]
  rfl

end FiniteCalculusProbability
end Gnosis
