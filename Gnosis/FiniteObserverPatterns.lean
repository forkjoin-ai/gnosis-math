import Gnosis.FiniteObserverCompactness

namespace Gnosis

/-!
# Finite Observer Patterns

Reusable compactness adapters for common bounded-discrete domains. Each pattern
exposes a Nat-valued residual, a scalar observer, and an `ObserverPromotion`
instance into the generic finite observer compactness theorem.
-/

structure ScalarObserver where
  tolerance : Nat
  deriving Repr, DecidableEq

def natBudgetMeasure : ObserverBudget Nat :=
  { total := id }

def natResidualAnswer (residual : Nat) (observer : ScalarObserver) (depth : Nat) : Prop :=
  residual ≤ observer.tolerance + depth

def natResidualSignature : RefinementSignature Nat ScalarObserver :=
  { answer := natResidualAnswer }

def natResidualPromotion
    (Lower LowerObserver : Type)
    (residual : Lower → LowerObserver → Nat) :
    ObserverPromotion Lower Nat LowerObserver ScalarObserver Nat :=
  { lowerResidual := residual
    promote := residual
    budgetMeasure := natBudgetMeasure
    higherSignature := natResidualSignature
    higherAcceptsOfBudget := by
      intro lower lowerObserver budget observer depth hresidual hbudget
      change residual lower lowerObserver ≤ observer.tolerance + depth
      exact Nat.le_trans hresidual
        (Nat.le_trans hbudget (Nat.le_add_left depth observer.tolerance)) }

theorem nat_residual_observer_compactness
    {Lower LowerObserver : Type}
    (residual : Lower → LowerObserver → Nat)
    (lower : Lower)
    (lowerObserver : LowerObserver)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hresidual : residual lower lowerObserver ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      ((natResidualPromotion Lower LowerObserver residual).promote lower lowerObserver)
      observer depth :=
  approximate_observer_compactness
    (natResidualPromotion Lower LowerObserver residual)
    lower lowerObserver budget wider observer depth
    hresidual hcovers hbudget

/-! ## Queue pattern -/

structure QueueResidualState where
  backlog : Nat
  serviceDebt : Nat
  deriving Repr, DecidableEq

def queueResidual (state : QueueResidualState) (_observer : Unit) : Nat :=
  state.backlog + state.serviceDebt

def queueObserverPromotion :
    ObserverPromotion QueueResidualState Nat Unit ScalarObserver Nat :=
  natResidualPromotion QueueResidualState Unit queueResidual

theorem queue_observer_compactness
    (state : QueueResidualState)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hresidual : queueResidual state () ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (queueObserverPromotion.promote state ()) observer depth :=
  approximate_observer_compactness queueObserverPromotion
    state () budget wider observer depth hresidual hcovers hbudget

/-! ## Thermodynamic pattern -/

structure ThermodynamicResidualState where
  heatLeak : Nat
  entropyDebt : Nat
  deriving Repr, DecidableEq

def thermodynamicResidual
    (state : ThermodynamicResidualState) (_observer : Unit) : Nat :=
  state.heatLeak + state.entropyDebt

def thermodynamicObserverPromotion :
    ObserverPromotion ThermodynamicResidualState Nat Unit ScalarObserver Nat :=
  natResidualPromotion ThermodynamicResidualState Unit thermodynamicResidual

theorem thermodynamic_observer_compactness
    (state : ThermodynamicResidualState)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hresidual : thermodynamicResidual state () ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (thermodynamicObserverPromotion.promote state ()) observer depth :=
  approximate_observer_compactness thermodynamicObserverPromotion
    state () budget wider observer depth hresidual hcovers hbudget

/-! ## Mesh routing pattern -/

structure MeshRoutingResidualState where
  unroutedPressure : Nat
  capacityDebt : Nat
  deriving Repr, DecidableEq

def meshRoutingResidual
    (state : MeshRoutingResidualState) (_observer : Unit) : Nat :=
  state.unroutedPressure + state.capacityDebt

def meshRoutingObserverPromotion :
    ObserverPromotion MeshRoutingResidualState Nat Unit ScalarObserver Nat :=
  natResidualPromotion MeshRoutingResidualState Unit meshRoutingResidual

theorem mesh_routing_observer_compactness
    (state : MeshRoutingResidualState)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hresidual : meshRoutingResidual state () ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (meshRoutingObserverPromotion.promote state ()) observer depth :=
  approximate_observer_compactness meshRoutingObserverPromotion
    state () budget wider observer depth hresidual hcovers hbudget

/-! ## Attention pattern -/

structure AttentionResidualState where
  missedWeight : Nat
  saturationDebt : Nat
  deriving Repr, DecidableEq

def attentionResidual
    (state : AttentionResidualState) (_observer : Unit) : Nat :=
  state.missedWeight + state.saturationDebt

def attentionObserverPromotion :
    ObserverPromotion AttentionResidualState Nat Unit ScalarObserver Nat :=
  natResidualPromotion AttentionResidualState Unit attentionResidual

theorem attention_observer_compactness
    (state : AttentionResidualState)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hresidual : attentionResidual state () ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (attentionObserverPromotion.promote state ()) observer depth :=
  approximate_observer_compactness attentionObserverPromotion
    state () budget wider observer depth hresidual hcovers hbudget

/-! ## Finite approximation pattern -/

structure FiniteApproximationResidualState where
  discretizationError : Nat
  truncationError : Nat
  deriving Repr, DecidableEq

def finiteApproximationResidual
    (state : FiniteApproximationResidualState) (_observer : Unit) : Nat :=
  state.discretizationError + state.truncationError

def finiteApproximationObserverPromotion :
    ObserverPromotion FiniteApproximationResidualState Nat Unit ScalarObserver Nat :=
  natResidualPromotion FiniteApproximationResidualState Unit finiteApproximationResidual

theorem finite_approximation_observer_compactness
    (state : FiniteApproximationResidualState)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hresidual : finiteApproximationResidual state () ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (finiteApproximationObserverPromotion.promote state ()) observer depth :=
  approximate_observer_compactness finiteApproximationObserverPromotion
    state () budget wider observer depth hresidual hcovers hbudget

end Gnosis
