import Gnosis.FiniteProbabilityCore.BayesTotalProbability

namespace Gnosis
namespace FiniteProbabilityCore
/-! ## Probability residual observers -/

structure ProbabilityResidualState where
  unobservedMass : Nat
  truncatedMass : Nat
  coarseningDebt : Nat
  deriving Repr, DecidableEq

def probabilityResidual
    (state : ProbabilityResidualState) (_observer : Unit) : Nat :=
  state.unobservedMass + state.truncatedMass + state.coarseningDebt

def probabilityObserverPromotion :
    ObserverPromotion ProbabilityResidualState Nat Unit ScalarObserver Nat :=
  natResidualPromotion ProbabilityResidualState Unit probabilityResidual

theorem probability_residual_monotone_budget
    (state : ProbabilityResidualState)
    (budget wider : Nat)
    (hresidual : probabilityResidual state () ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider) :
    probabilityResidual state () ≤ wider :=
  Nat.le_trans hresidual hcovers

theorem probability_no_hidden_defect
    (state : ProbabilityResidualState)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hresidual : probabilityResidual state () ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote state ()) observer depth :=
  approximate_observer_compactness probabilityObserverPromotion
    state () budget wider observer depth hresidual hcovers hbudget

end FiniteProbabilityCore
end Gnosis
