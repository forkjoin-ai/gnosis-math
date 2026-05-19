import Gnosis.RefinementSignature

namespace Gnosis

/-!
# Finite Observer Compactness

Generic compactness interface for bounded finite observers. A lower observer
layer can promote into a higher observer layer when residuals are bounded by
budgets and those budgets are accepted by monotone higher observers.
-/

structure ObserverBudget (Budget : Type) where
  total : Budget → Nat

def ObserverBudgetCovers
    {Budget : Type}
    (measure : ObserverBudget Budget)
    (budget wider : Budget) : Prop :=
  measure.total budget ≤ measure.total wider

theorem observer_budget_covers_refl
    {Budget : Type}
    (measure : ObserverBudget Budget)
    (budget : Budget) :
    ObserverBudgetCovers measure budget budget :=
  Nat.le_refl (measure.total budget)

theorem observer_budget_covers_trans
    {Budget : Type}
    (measure : ObserverBudget Budget)
    (left middle right : Budget)
    (hleftMiddle : ObserverBudgetCovers measure left middle)
    (hmiddleRight : ObserverBudgetCovers measure middle right) :
    ObserverBudgetCovers measure left right :=
  Nat.le_trans hleftMiddle hmiddleRight

structure ObserverPromotion
    (Lower Higher LowerObserver HigherObserver Budget : Type) where
  lowerResidual : Lower → LowerObserver → Nat
  promote : Lower → LowerObserver → Higher
  budgetMeasure : ObserverBudget Budget
  higherSignature : RefinementSignature Higher HigherObserver
  higherAcceptsOfBudget :
    ∀ lower : Lower, ∀ lowerObserver : LowerObserver,
      ∀ budget : Budget, ∀ higherObserver : HigherObserver, ∀ depth : Nat,
        lowerResidual lower lowerObserver ≤ budgetMeasure.total budget →
          budgetMeasure.total budget ≤ depth →
            higherSignature.answer
              (promote lower lowerObserver) higherObserver depth

theorem observer_compactness
    {Lower Higher LowerObserver HigherObserver Budget : Type}
    (promotion :
      ObserverPromotion Lower Higher LowerObserver HigherObserver Budget)
    (lower : Lower)
    (lowerObserver : LowerObserver)
    (budget : Budget)
    (higherObserver : HigherObserver)
    (depth : Nat)
    (hresidual :
      promotion.lowerResidual lower lowerObserver ≤
        promotion.budgetMeasure.total budget)
    (hbudget : promotion.budgetMeasure.total budget ≤ depth) :
    promotion.higherSignature.answer
      (promotion.promote lower lowerObserver) higherObserver depth :=
  promotion.higherAcceptsOfBudget
    lower lowerObserver budget higherObserver depth hresidual hbudget

theorem approximate_observer_compactness
    {Lower Higher LowerObserver HigherObserver Budget : Type}
    (promotion :
      ObserverPromotion Lower Higher LowerObserver HigherObserver Budget)
    (lower : Lower)
    (lowerObserver : LowerObserver)
    (budget wider : Budget)
    (higherObserver : HigherObserver)
    (depth : Nat)
    (hresidual :
      promotion.lowerResidual lower lowerObserver ≤
        promotion.budgetMeasure.total budget)
    (hcovers : ObserverBudgetCovers promotion.budgetMeasure budget wider)
    (hbudget : promotion.budgetMeasure.total wider ≤ depth) :
    promotion.higherSignature.answer
      (promotion.promote lower lowerObserver) higherObserver depth :=
  observer_compactness promotion lower lowerObserver wider higherObserver depth
    (Nat.le_trans hresidual hcovers)
    hbudget

theorem exact_observer_collapse
    {Lower Higher LowerObserver HigherObserver Budget : Type}
    (promotion :
      ObserverPromotion Lower Higher LowerObserver HigherObserver Budget)
    (lower : Lower)
    (lowerObserver : LowerObserver)
    (zeroBudget : Budget)
    (higherObserver : HigherObserver)
    (depth : Nat)
    (hzeroResidual : promotion.lowerResidual lower lowerObserver = 0)
    (hzeroBudget : promotion.budgetMeasure.total zeroBudget = 0) :
    promotion.higherSignature.answer
      (promotion.promote lower lowerObserver) higherObserver depth := by
  apply observer_compactness promotion lower lowerObserver zeroBudget higherObserver depth
  · rw [hzeroResidual]
    exact Nat.zero_le (promotion.budgetMeasure.total zeroBudget)
  · rw [hzeroBudget]
    exact Nat.zero_le depth

theorem no_hidden_defect_of_promoted_observer
    {Lower Higher LowerObserver HigherObserver Budget : Type}
    (promotion :
      ObserverPromotion Lower Higher LowerObserver HigherObserver Budget)
    (lower : Lower)
    (lowerObserver : LowerObserver)
    (budget wider : Budget)
    (hresidual :
      promotion.lowerResidual lower lowerObserver ≤
        promotion.budgetMeasure.total budget)
    (hcovers : ObserverBudgetCovers promotion.budgetMeasure budget wider) :
    ∀ higherObserver : HigherObserver, ∀ depth : Nat,
      promotion.budgetMeasure.total wider ≤ depth →
        promotion.higherSignature.answer
          (promotion.promote lower lowerObserver) higherObserver depth := by
  intro higherObserver depth hbudget
  exact approximate_observer_compactness
    promotion lower lowerObserver budget wider higherObserver depth
    hresidual hcovers hbudget

end Gnosis
