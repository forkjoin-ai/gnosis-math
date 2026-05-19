import Gnosis.FiniteProbabilityCore.ProcessesChains

namespace Gnosis
namespace FiniteProbabilityCore
/-! ## Finite approximation towers -/

structure ApproximationStep where
  depth : Nat
  process : FiniteProbabilityProcess
  deriving Repr

def ApproximationStep.shadow
    (step : ApproximationStep) : Nat :=
  step.process.residual

def approximationTowerResidual : List ApproximationStep → Nat
  | [] => 0
  | step :: rest => step.shadow + approximationTowerResidual rest

def approximationTowerDepth : List ApproximationStep → Nat
  | [] => 0
  | step :: rest => step.depth + approximationTowerDepth rest

theorem approximation_tower_residual_append
    (left right : List ApproximationStep) :
    approximationTowerResidual (left ++ right) =
      approximationTowerResidual left + approximationTowerResidual right := by
  induction left with
  | nil => simp [approximationTowerResidual]
  | cons step rest ih =>
      simp [approximationTowerResidual, ih, Nat.add_assoc]

theorem approximation_tower_depth_append
    (left right : List ApproximationStep) :
    approximationTowerDepth (left ++ right) =
      approximationTowerDepth left + approximationTowerDepth right := by
  induction left with
  | nil => simp [approximationTowerDepth]
  | cons step rest ih =>
      simp [approximationTowerDepth, ih, Nat.add_assoc]

def ApproximationStep.refines
    (coarse fine : ApproximationStep) : Prop :=
  fine.depth ≥ coarse.depth ∧ fine.shadow ≤ coarse.shadow

theorem approximation_step_refines_refl
    (step : ApproximationStep) :
    step.refines step :=
  ⟨Nat.le_refl step.depth, Nat.le_refl step.shadow⟩

theorem approximation_step_refines_trans
    (coarse middle fine : ApproximationStep)
    (hleft : coarse.refines middle)
    (hright : middle.refines fine) :
    coarse.refines fine :=
  ⟨Nat.le_trans hleft.1 hright.1,
    Nat.le_trans hright.2 hleft.2⟩

theorem approximation_step_refinement_preserves_acceptance
    (coarse fine : ApproximationStep)
    (observer : ScalarObserver)
    (depth : Nat)
    (hrefines : coarse.refines fine)
    (haccepts :
      natResidualSignature.answer
        (probabilityObserverPromotion.promote coarse.process.residualState ())
        observer depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote fine.process.residualState ())
      observer depth := by
  have hshadow : fine.process.residual ≤ coarse.process.residual := by
    change fine.process.residual ≤ coarse.process.residual
    exact hrefines.2
  unfold natResidualSignature natResidualAnswer at haccepts ⊢
  unfold probabilityObserverPromotion natResidualPromotion at haccepts ⊢
  simp [process_residual_state_eq_residual] at haccepts ⊢
  exact Nat.le_trans hshadow haccepts

structure ApproximationTower where
  base : ApproximationStep
  steps : List ApproximationStep
  residualBound : Nat
  residualBounded : approximationTowerResidual steps ≤ residualBound
  deriving Repr

def ApproximationTower.totalDepth
    (tower : ApproximationTower) : Nat :=
  tower.base.depth + approximationTowerDepth tower.steps

def ApproximationTower.totalShadow
    (tower : ApproximationTower) : Nat :=
  tower.base.shadow + approximationTowerResidual tower.steps

theorem approximation_tower_shadow_bounded
    (tower : ApproximationTower) :
    tower.totalShadow ≤ tower.base.shadow + tower.residualBound := by
  unfold ApproximationTower.totalShadow
  exact Nat.add_le_add_left tower.residualBounded tower.base.shadow

theorem approximation_tower_no_hidden_defect
    (tower : ApproximationTower)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hbase : tower.base.shadow + tower.residualBound ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote
        { unobservedMass := tower.totalShadow,
          truncatedMass := 0,
          coarseningDebt := 0 } ())
      observer depth := by
  apply probability_no_hidden_defect
  · simp [probabilityResidual]
    exact Nat.le_trans (approximation_tower_shadow_bounded tower) hbase
  · exact hcovers
  · exact hbudget

def ApproximationTower.refines
    (coarse fine : ApproximationTower) : Prop :=
  coarse.base.refines fine.base ∧ fine.totalShadow ≤ coarse.totalShadow

theorem approximation_tower_refines_refl
    (tower : ApproximationTower) :
    tower.refines tower :=
  ⟨approximation_step_refines_refl tower.base,
    Nat.le_refl tower.totalShadow⟩

theorem approximation_tower_refines_trans
    (coarse middle fine : ApproximationTower)
    (hleft : coarse.refines middle)
    (hright : middle.refines fine) :
    coarse.refines fine :=
  ⟨approximation_step_refines_trans coarse.base middle.base fine.base
      hleft.1 hright.1,
    Nat.le_trans hright.2 hleft.2⟩

theorem approximation_tower_refinement_preserves_bound
    (coarse fine : ApproximationTower)
    (budget : Nat)
    (hrefines : coarse.refines fine)
    (hcoarse : coarse.totalShadow ≤ budget) :
    fine.totalShadow ≤ budget :=
  Nat.le_trans hrefines.2 hcoarse

theorem approximation_tower_refinement_preserves_acceptance
    (coarse fine : ApproximationTower)
    (budget wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hrefines : coarse.refines fine)
    (hcoarse : coarse.totalShadow ≤ budget)
    (hcovers : ObserverBudgetCovers natBudgetMeasure budget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote
        { unobservedMass := fine.totalShadow,
          truncatedMass := 0,
          coarseningDebt := 0 } ())
      observer depth := by
  apply probability_no_hidden_defect
  · simp [probabilityResidual]
    exact approximation_tower_refinement_preserves_bound
      coarse fine budget hrefines hcoarse
  · exact hcovers
  · exact hbudget

structure ApproximationShrinkCertificate where
  coarse : ApproximationTower
  fine : ApproximationTower
  savedShadow : Nat
  shrinksBy : fine.totalShadow + savedShadow = coarse.totalShadow
  deriving Repr

theorem approximation_shrink_certificate_refines
    (certificate : ApproximationShrinkCertificate)
    (hbase : certificate.coarse.base.refines certificate.fine.base) :
    certificate.coarse.refines certificate.fine := by
  constructor
  · exact hbase
  · rw [← certificate.shrinksBy]
    exact Nat.le_add_right certificate.fine.totalShadow
      certificate.savedShadow

end FiniteProbabilityCore
end Gnosis
