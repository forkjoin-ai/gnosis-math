import Gnosis.FiniteProbabilityCore.Processes

namespace Gnosis
namespace FiniteProbabilityCore
/-! ## Process chains and bounded shadow equivalence -/

def processListMassLoss : List FiniteProbabilityProcess → Nat
  | [] => 0
  | process :: rest => process.massLoss + processListMassLoss rest

def processListResidual : List FiniteProbabilityProcess → Nat
  | [] => 0
  | process :: rest => process.residual + processListResidual rest

theorem process_list_mass_loss_append
    (left right : List FiniteProbabilityProcess) :
    processListMassLoss (left ++ right) =
      processListMassLoss left + processListMassLoss right := by
  induction left with
  | nil => simp [processListMassLoss]
  | cons process rest ih =>
      simp [processListMassLoss, ih, Nat.add_assoc]

theorem process_list_residual_append
    (left right : List FiniteProbabilityProcess) :
    processListResidual (left ++ right) =
      processListResidual left + processListResidual right := by
  induction left with
  | nil => simp [processListResidual]
  | cons process rest ih =>
      simp [processListResidual, ih, Nat.add_assoc]

theorem process_list_loss_covered_by_residual
    (processes : List FiniteProbabilityProcess) :
    processListMassLoss processes ≤ processListResidual processes := by
  induction processes with
  | nil => simp [processListMassLoss, processListResidual]
  | cons process rest ih =>
      simp [processListMassLoss, processListResidual]
      exact Nat.add_le_add process.lossCovered ih

structure FiniteProbabilityProcessChain where
  input : FiniteDistribution
  output : FiniteDistribution
  processes : List FiniteProbabilityProcess
  massLoss : Nat
  residual : Nat
  balance : output.totalMass + massLoss = input.totalMass
  massLossAccounts : massLoss = processListMassLoss processes
  residualAccounts : residual = processListResidual processes
  deriving Repr

def FiniteProbabilityProcessChain.residualState
    (chain : FiniteProbabilityProcessChain) : ProbabilityResidualState :=
  { unobservedMass := chain.residual
    truncatedMass := 0
    coarseningDebt := 0 }

theorem process_chain_residual_state_eq_residual
    (chain : FiniteProbabilityProcessChain) :
    probabilityResidual chain.residualState () =
      chain.residual := by
  simp [FiniteProbabilityProcessChain.residualState, probabilityResidual]

theorem process_chain_loss_covered_by_residual
    (chain : FiniteProbabilityProcessChain) :
    chain.massLoss ≤ chain.residual := by
  rw [chain.massLossAccounts, chain.residualAccounts]
  exact process_list_loss_covered_by_residual chain.processes

theorem process_chain_no_hidden_defect
    (chain : FiniteProbabilityProcessChain)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hresidual : chain.residual ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote chain.residualState ())
      observer depth := by
  apply probability_no_hidden_defect
  · rwa [process_chain_residual_state_eq_residual]
  · exact hcovers
  · exact hbudget

def natAbsDiff (left right : Nat) : Nat :=
  (left - right) + (right - left)

def ProcessShadowEquivalent
    (budget : Nat)
    (left right : FiniteProbabilityProcess) : Prop :=
  natAbsDiff left.residual right.residual ≤ budget

theorem process_shadow_equivalent_refl
    (budget : Nat)
    (process : FiniteProbabilityProcess) :
    ProcessShadowEquivalent budget process process := by
  unfold ProcessShadowEquivalent natAbsDiff
  simp

theorem process_shadow_equivalent_symm
    (budget : Nat)
    (left right : FiniteProbabilityProcess)
    (hequivalent : ProcessShadowEquivalent budget left right) :
    ProcessShadowEquivalent budget right left := by
  unfold ProcessShadowEquivalent natAbsDiff at hequivalent ⊢
  rw [Nat.add_comm]
  exact hequivalent

theorem nat_abs_diff_triangle
    (left middle right : Nat) :
    natAbsDiff left right ≤
      natAbsDiff left middle + natAbsDiff middle right := by
  unfold natAbsDiff
  omega

theorem process_shadow_equivalent_trans_add
    (left middle right : FiniteProbabilityProcess)
    (leftBudget rightBudget : Nat)
    (hleft :
      ProcessShadowEquivalent leftBudget left middle)
    (hright :
      ProcessShadowEquivalent rightBudget middle right) :
    ProcessShadowEquivalent (leftBudget + rightBudget) left right := by
  unfold ProcessShadowEquivalent at hleft hright ⊢
  exact Nat.le_trans
    (nat_abs_diff_triangle left.residual middle.residual right.residual)
    (Nat.add_le_add hleft hright)

theorem process_shadow_equivalent_observer_accepts
    (left right : FiniteProbabilityProcess)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hequivalent : ProcessShadowEquivalent budget left right)
    (hleft : left.residual ≤ observer.tolerance)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote right.residualState ())
      observer (left.residual + depth) := by
  unfold ProcessShadowEquivalent natAbsDiff at hequivalent
  unfold probabilityObserverPromotion natResidualPromotion
  unfold natResidualSignature natResidualAnswer
  simp [process_residual_state_eq_residual]
  have hdiff : right.residual - left.residual ≤ budget :=
    Nat.le_trans (Nat.le_add_left (right.residual - left.residual)
      (left.residual - right.residual)) hequivalent
  have hcovered : budget ≤ depth :=
    Nat.le_trans hcovers hbudget
  omega

end FiniteProbabilityCore
end Gnosis
