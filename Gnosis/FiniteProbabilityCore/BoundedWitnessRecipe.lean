import Gnosis.FiniteProbabilityCore.BoundedWitnessInterface

namespace Gnosis
namespace FiniteProbabilityCore

/-!
# Bounded Witness Recipe

Minimal recipe for a new bounded domain:

1. Define a residual state.
2. Define one residual function.
3. Package it as `BoundedWitnessAdapter`.
4. Inherit witness construction, shadow coverage, pipeline accounting, and
   process-chain lowering.
-/

structure ToyResidualState where
  visibleDebt : Nat
  hiddenDebt : Nat
  deriving Repr, DecidableEq

def toyResidual (state : ToyResidualState) : Nat :=
  state.visibleDebt + state.hiddenDebt

def toyBoundedWitnessAdapter :
    BoundedWitnessAdapter ToyResidualState :=
  { domainName := "toy"
    residual := toyResidual }

def toyBoundedWitnessExample :
    RuntimeBoundedWitnessCertificate :=
  toyBoundedWitnessAdapter.toWitness
    1 { visibleDebt := 2, hiddenDebt := 3 } 5 (by native_decide)

theorem toy_bounded_witness_shadow_covered :
    toyBoundedWitnessExample.residualShadow ≤
      toyBoundedWitnessExample.observerBudget :=
  runtime_bounded_witness_shadow_covered toyBoundedWitnessExample

def toyBoundedWitnessPipelineExample :
    RuntimeBoundedWitnessPipeline :=
  { witnesses := [toyBoundedWitnessExample]
    residualShadow := 5
    observerBudget := 5
    residualAccounts := by native_decide
    accepted := Nat.le_refl 5 }

theorem toy_bounded_witness_pipeline_residual :
    (witnessBoundedPipelineTheorem
      toyBoundedWitnessPipelineExample).residualShadow =
      (witnessBoundedPipelineTheorem
        toyBoundedWitnessPipelineExample).witnessResidualSum :=
  witness_bounded_pipeline_theorem_sound toyBoundedWitnessPipelineExample

theorem toy_bounded_witness_process_chain_residual :
    toyBoundedWitnessPipelineExample.toProcessChain.residual = 5 :=
  rfl

theorem toy_bounded_witness_no_hidden_defect
    (wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hcovers : ObserverBudgetCovers natBudgetMeasure 5 wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote
        toyBoundedWitnessPipelineExample.toProcessChain.residualState ())
      observer depth :=
  runtime_bounded_witness_pipeline_process_chain_no_hidden_defect
    toyBoundedWitnessPipelineExample wider observer depth hcovers hbudget

end FiniteProbabilityCore
end Gnosis
