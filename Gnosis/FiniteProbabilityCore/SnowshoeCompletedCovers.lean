import Gnosis.FiniteProbabilityCore.ApproximationTowers

namespace Gnosis
namespace FiniteProbabilityCore
/-! ## Finite horizons and snowshoe coverage -/

structure FiniteHorizon where
  depth : Nat
  residualBudget : Nat
  deriving Repr, DecidableEq

def FiniteHorizon.sees
    (horizon : FiniteHorizon)
    (tower : ApproximationTower) : Prop :=
  tower.totalDepth ≤ horizon.depth ∧
    tower.totalShadow ≤ horizon.residualBudget

theorem finite_horizon_sees_of_refinement
    (horizon : FiniteHorizon)
    (coarse fine : ApproximationTower)
    (hrefines : coarse.refines fine)
    (hdepth : fine.totalDepth ≤ horizon.depth)
    (hcoarse : coarse.totalShadow ≤ horizon.residualBudget) :
    horizon.sees fine :=
  ⟨hdepth, Nat.le_trans hrefines.2 hcoarse⟩

structure CompletedInfiniteInterface where
  horizon : FiniteHorizon
  tower : ApproximationTower
  witnessed : horizon.sees tower
  deriving Repr

def CompletedInfiniteInterface.visibleDepth
    (interface : CompletedInfiniteInterface) : Nat :=
  interface.tower.totalDepth

def CompletedInfiniteInterface.shadow
    (interface : CompletedInfiniteInterface) : Nat :=
  interface.tower.totalShadow

theorem completed_infinite_shadow_within_horizon
    (interface : CompletedInfiniteInterface) :
    interface.shadow ≤ interface.horizon.residualBudget :=
  interface.witnessed.2

theorem completed_infinite_depth_within_horizon
    (interface : CompletedInfiniteInterface) :
    interface.visibleDepth ≤ interface.horizon.depth :=
  interface.witnessed.1

theorem completed_infinite_no_hidden_defect
    (interface : CompletedInfiniteInterface)
    (wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hcovers :
      ObserverBudgetCovers natBudgetMeasure
        interface.horizon.residualBudget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote
        { unobservedMass := interface.shadow,
          truncatedMass := 0,
          coarseningDebt := 0 } ())
      observer depth := by
  apply probability_no_hidden_defect
  · simp [probabilityResidual]
    exact completed_infinite_shadow_within_horizon interface
  · exact hcovers
  · exact hbudget

structure SnowshoePatch where
  footprint : Nat
  shadow : Nat
  deriving Repr, DecidableEq

def snowshoePatchCovered
    (patch : SnowshoePatch)
    (horizon : FiniteHorizon) : Prop :=
  patch.footprint ≤ horizon.depth ∧ patch.shadow ≤ horizon.residualBudget

def snowshoeFootprint : List SnowshoePatch → Nat
  | [] => 0
  | patch :: rest => patch.footprint + snowshoeFootprint rest

def snowshoeShadow : List SnowshoePatch → Nat
  | [] => 0
  | patch :: rest => patch.shadow + snowshoeShadow rest

theorem snowshoe_footprint_append
    (left right : List SnowshoePatch) :
    snowshoeFootprint (left ++ right) =
      snowshoeFootprint left + snowshoeFootprint right := by
  induction left with
  | nil => simp [snowshoeFootprint]
  | cons patch rest ih =>
      simp [snowshoeFootprint, ih, Nat.add_assoc]

theorem snowshoe_shadow_append
    (left right : List SnowshoePatch) :
    snowshoeShadow (left ++ right) =
      snowshoeShadow left + snowshoeShadow right := by
  induction left with
  | nil => simp [snowshoeShadow]
  | cons patch rest ih =>
      simp [snowshoeShadow, ih, Nat.add_assoc]

structure SnowshoeSurface where
  patches : List SnowshoePatch
  horizon : FiniteHorizon
  footprintBounded : snowshoeFootprint patches ≤ horizon.depth
  shadowBounded : snowshoeShadow patches ≤ horizon.residualBudget
  deriving Repr

def SnowshoeSurface.toCompletedInterface
    (surface : SnowshoeSurface)
    (tower : ApproximationTower)
    (hdepth : tower.totalDepth ≤ snowshoeFootprint surface.patches)
    (hshadow : tower.totalShadow ≤ snowshoeShadow surface.patches) :
    CompletedInfiniteInterface :=
  { horizon := surface.horizon
    tower := tower
    witnessed :=
      ⟨Nat.le_trans hdepth surface.footprintBounded,
        Nat.le_trans hshadow surface.shadowBounded⟩ }

theorem snowshoe_surface_no_hidden_defect
    (surface : SnowshoeSurface)
    (tower : ApproximationTower)
    (hdepth : tower.totalDepth ≤ snowshoeFootprint surface.patches)
    (hshadow : tower.totalShadow ≤ snowshoeShadow surface.patches)
    (wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hcovers :
      ObserverBudgetCovers natBudgetMeasure
        surface.horizon.residualBudget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote
        { unobservedMass :=
            (surface.toCompletedInterface tower hdepth hshadow).shadow,
          truncatedMass := 0,
          coarseningDebt := 0 } ())
      observer depth :=
  completed_infinite_no_hidden_defect
    (surface.toCompletedInterface tower hdepth hshadow)
    wider observer depth hcovers hbudget

def snowshoePatchUnion
    (left right : SnowshoePatch) : SnowshoePatch :=
  { footprint := left.footprint + right.footprint
    shadow := left.shadow + right.shadow }

theorem snowshoe_patch_union_covered
    (left right : SnowshoePatch)
    (horizon : FiniteHorizon)
    (hfootprint :
      left.footprint + right.footprint ≤ horizon.depth)
    (hshadow :
      left.shadow + right.shadow ≤ horizon.residualBudget) :
    snowshoePatchCovered (snowshoePatchUnion left right) horizon :=
  ⟨hfootprint, hshadow⟩

structure FiniteSurfaceExhaustion where
  surface : SnowshoeSurface
  tower : ApproximationTower
  depthExact : tower.totalDepth = snowshoeFootprint surface.patches
  shadowExact : tower.totalShadow = snowshoeShadow surface.patches
  deriving Repr

def FiniteSurfaceExhaustion.interface
    (exhaustion : FiniteSurfaceExhaustion) : CompletedInfiniteInterface :=
  exhaustion.surface.toCompletedInterface exhaustion.tower
    (by
      rw [exhaustion.depthExact]
      exact Nat.le_refl _)
    (by
      rw [exhaustion.shadowExact]
      exact Nat.le_refl _)

theorem finite_surface_exhaustion_depth_eq_surface
    (exhaustion : FiniteSurfaceExhaustion) :
    exhaustion.interface.visibleDepth =
      snowshoeFootprint exhaustion.surface.patches := by
  unfold FiniteSurfaceExhaustion.interface
  unfold CompletedInfiniteInterface.visibleDepth
  exact exhaustion.depthExact

theorem finite_surface_exhaustion_shadow_eq_surface
    (exhaustion : FiniteSurfaceExhaustion) :
    exhaustion.interface.shadow =
      snowshoeShadow exhaustion.surface.patches := by
  unfold FiniteSurfaceExhaustion.interface
  unfold CompletedInfiniteInterface.shadow
  exact exhaustion.shadowExact

theorem finite_surface_exhaustion_no_hidden_defect
    (exhaustion : FiniteSurfaceExhaustion)
    (wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hcovers :
      ObserverBudgetCovers natBudgetMeasure
        exhaustion.surface.horizon.residualBudget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote
        { unobservedMass := exhaustion.interface.shadow,
          truncatedMass := 0,
          coarseningDebt := 0 } ())
      observer depth :=
  completed_infinite_no_hidden_defect
    exhaustion.interface wider observer depth hcovers hbudget

def FiniteHorizon.append
    (left right : FiniteHorizon) : FiniteHorizon :=
  { depth := left.depth + right.depth
    residualBudget := left.residualBudget + right.residualBudget }

theorem finite_horizon_append_depth
    (left right : FiniteHorizon) :
    (left.append right).depth = left.depth + right.depth := rfl

theorem finite_horizon_append_residual_budget
    (left right : FiniteHorizon) :
    (left.append right).residualBudget =
      left.residualBudget + right.residualBudget := rfl

def SnowshoeSurface.append
    (left right : SnowshoeSurface) : SnowshoeSurface :=
  { patches := left.patches ++ right.patches
    horizon := left.horizon.append right.horizon
    footprintBounded := by
      rw [snowshoe_footprint_append]
      exact Nat.add_le_add left.footprintBounded right.footprintBounded
    shadowBounded := by
      rw [snowshoe_shadow_append]
      exact Nat.add_le_add left.shadowBounded right.shadowBounded }

theorem snowshoe_surface_append_footprint
    (left right : SnowshoeSurface) :
    snowshoeFootprint (left.append right).patches =
      snowshoeFootprint left.patches + snowshoeFootprint right.patches := by
  exact snowshoe_footprint_append left.patches right.patches

theorem snowshoe_surface_append_shadow
    (left right : SnowshoeSurface) :
    snowshoeShadow (left.append right).patches =
      snowshoeShadow left.patches + snowshoeShadow right.patches := by
  exact snowshoe_shadow_append left.patches right.patches

structure CompletedInterfaceComposite where
  left : CompletedInfiniteInterface
  right : CompletedInfiniteInterface
  deriving Repr

def CompletedInterfaceComposite.horizon
    (composite : CompletedInterfaceComposite) : FiniteHorizon :=
  composite.left.horizon.append composite.right.horizon

def CompletedInterfaceComposite.depth
    (composite : CompletedInterfaceComposite) : Nat :=
  composite.left.visibleDepth + composite.right.visibleDepth

def CompletedInterfaceComposite.shadow
    (composite : CompletedInterfaceComposite) : Nat :=
  composite.left.shadow + composite.right.shadow

theorem completed_interface_composite_depth_bounded
    (composite : CompletedInterfaceComposite) :
    composite.depth ≤ composite.horizon.depth := by
  unfold CompletedInterfaceComposite.depth
  unfold CompletedInterfaceComposite.horizon
  exact Nat.add_le_add
    (completed_infinite_depth_within_horizon composite.left)
    (completed_infinite_depth_within_horizon composite.right)

theorem completed_interface_composite_shadow_bounded
    (composite : CompletedInterfaceComposite) :
    composite.shadow ≤ composite.horizon.residualBudget := by
  unfold CompletedInterfaceComposite.shadow
  unfold CompletedInterfaceComposite.horizon
  exact Nat.add_le_add
    (completed_infinite_shadow_within_horizon composite.left)
    (completed_infinite_shadow_within_horizon composite.right)

theorem completed_interface_composite_no_hidden_defect
    (composite : CompletedInterfaceComposite)
    (wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hcovers :
      ObserverBudgetCovers natBudgetMeasure
        composite.horizon.residualBudget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote
        { unobservedMass := composite.shadow,
          truncatedMass := 0,
          coarseningDebt := 0 } ())
      observer depth := by
  apply probability_no_hidden_defect
  · simp [probabilityResidual]
    exact completed_interface_composite_shadow_bounded composite
  · exact hcovers
  · exact hbudget

def FiniteSurfaceExhaustion.append
    (left right : FiniteSurfaceExhaustion)
    (tower : ApproximationTower)
    (hdepth :
      tower.totalDepth =
        snowshoeFootprint (left.surface.append right.surface).patches)
    (hshadow :
      tower.totalShadow =
        snowshoeShadow (left.surface.append right.surface).patches) :
    FiniteSurfaceExhaustion :=
  { surface := left.surface.append right.surface
    tower := tower
    depthExact := hdepth
    shadowExact := hshadow }

theorem finite_surface_exhaustion_append_surface_depth
    (left right : FiniteSurfaceExhaustion)
    (tower : ApproximationTower)
    (hdepth :
      tower.totalDepth =
        snowshoeFootprint (left.surface.append right.surface).patches)
    (hshadow :
      tower.totalShadow =
        snowshoeShadow (left.surface.append right.surface).patches) :
    (left.append right tower hdepth hshadow).interface.visibleDepth =
      snowshoeFootprint left.surface.patches +
        snowshoeFootprint right.surface.patches := by
  rw [finite_surface_exhaustion_depth_eq_surface]
  exact snowshoe_surface_append_footprint left.surface right.surface

theorem finite_surface_exhaustion_append_surface_shadow
    (left right : FiniteSurfaceExhaustion)
    (tower : ApproximationTower)
    (hdepth :
      tower.totalDepth =
        snowshoeFootprint (left.surface.append right.surface).patches)
    (hshadow :
      tower.totalShadow =
        snowshoeShadow (left.surface.append right.surface).patches) :
    (left.append right tower hdepth hshadow).interface.shadow =
      snowshoeShadow left.surface.patches +
        snowshoeShadow right.surface.patches := by
  rw [finite_surface_exhaustion_shadow_eq_surface]
  exact snowshoe_surface_append_shadow left.surface right.surface

def SnowshoeSurface.refines
    (coarse fine : SnowshoeSurface) : Prop :=
  fine.horizon.depth ≥ coarse.horizon.depth ∧
    fine.horizon.residualBudget ≤ coarse.horizon.residualBudget ∧
    snowshoeFootprint fine.patches ≥ snowshoeFootprint coarse.patches ∧
    snowshoeShadow fine.patches ≤ snowshoeShadow coarse.patches

theorem snowshoe_surface_refines_refl
    (surface : SnowshoeSurface) :
    surface.refines surface :=
  ⟨Nat.le_refl surface.horizon.depth,
    Nat.le_refl surface.horizon.residualBudget,
    Nat.le_refl (snowshoeFootprint surface.patches),
    Nat.le_refl (snowshoeShadow surface.patches)⟩

theorem snowshoe_surface_refines_trans
    (coarse middle fine : SnowshoeSurface)
    (hleft : coarse.refines middle)
    (hright : middle.refines fine) :
    coarse.refines fine :=
  ⟨Nat.le_trans hleft.1 hright.1,
    Nat.le_trans hright.2.1 hleft.2.1,
    Nat.le_trans hleft.2.2.1 hright.2.2.1,
    Nat.le_trans hright.2.2.2 hleft.2.2.2⟩

theorem snowshoe_surface_refinement_preserves_shadow_bound
    (coarse fine : SnowshoeSurface)
    (hrefines : coarse.refines fine)
    (hshadow : snowshoeShadow coarse.patches ≤ coarse.horizon.residualBudget) :
    snowshoeShadow fine.patches ≤ coarse.horizon.residualBudget :=
  Nat.le_trans hrefines.2.2.2 hshadow

structure SnowshoeSurfaceShrink where
  coarse : SnowshoeSurface
  fine : SnowshoeSurface
  savedShadow : Nat
  footprintGrowth : Nat
  shadowShrinks :
    snowshoeShadow fine.patches + savedShadow =
      snowshoeShadow coarse.patches
  footprintGrows :
    snowshoeFootprint coarse.patches + footprintGrowth =
      snowshoeFootprint fine.patches
  deriving Repr

theorem snowshoe_surface_shrink_refines
    (certificate : SnowshoeSurfaceShrink)
    (hdepth :
      certificate.coarse.horizon.depth ≤ certificate.fine.horizon.depth)
    (hbudget :
      certificate.fine.horizon.residualBudget ≤
        certificate.coarse.horizon.residualBudget) :
    certificate.coarse.refines certificate.fine := by
  constructor
  · exact hdepth
  constructor
  · exact hbudget
  constructor
  · rw [← certificate.footprintGrows]
    exact Nat.le_add_right
      (snowshoeFootprint certificate.coarse.patches)
      certificate.footprintGrowth
  · rw [← certificate.shadowShrinks]
    exact Nat.le_add_right
      (snowshoeShadow certificate.fine.patches)
      certificate.savedShadow

/-! ## Generic finite covers -/

structure FiniteCover where
  footprint : Nat
  shadow : Nat
  horizon : FiniteHorizon
  footprintBounded : footprint ≤ horizon.depth
  shadowBounded : shadow ≤ horizon.residualBudget
  deriving Repr

def FiniteCover.append
    (left right : FiniteCover) : FiniteCover :=
  { footprint := left.footprint + right.footprint
    shadow := left.shadow + right.shadow
    horizon := left.horizon.append right.horizon
    footprintBounded :=
      Nat.add_le_add left.footprintBounded right.footprintBounded
    shadowBounded :=
      Nat.add_le_add left.shadowBounded right.shadowBounded }

theorem finite_cover_append_footprint
    (left right : FiniteCover) :
    (left.append right).footprint =
      left.footprint + right.footprint := rfl

theorem finite_cover_append_shadow
    (left right : FiniteCover) :
    (left.append right).shadow =
      left.shadow + right.shadow := rfl

def FiniteCover.refines
    (coarse fine : FiniteCover) : Prop :=
  coarse.footprint ≤ fine.footprint ∧
    fine.shadow ≤ coarse.shadow ∧
    coarse.horizon.depth ≤ fine.horizon.depth ∧
    fine.horizon.residualBudget ≤ coarse.horizon.residualBudget

theorem finite_cover_refines_refl
    (cover : FiniteCover) :
    cover.refines cover :=
  ⟨Nat.le_refl cover.footprint,
    Nat.le_refl cover.shadow,
    Nat.le_refl cover.horizon.depth,
    Nat.le_refl cover.horizon.residualBudget⟩

theorem finite_cover_refines_trans
    (coarse middle fine : FiniteCover)
    (hleft : coarse.refines middle)
    (hright : middle.refines fine) :
    coarse.refines fine :=
  ⟨Nat.le_trans hleft.1 hright.1,
    Nat.le_trans hright.2.1 hleft.2.1,
    Nat.le_trans hleft.2.2.1 hright.2.2.1,
    Nat.le_trans hright.2.2.2 hleft.2.2.2⟩

theorem finite_cover_no_hidden_defect
    (cover : FiniteCover)
    (wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hcovers :
      ObserverBudgetCovers natBudgetMeasure cover.horizon.residualBudget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote
        { unobservedMass := cover.shadow,
          truncatedMass := 0,
          coarseningDebt := 0 } ())
      observer depth := by
  apply probability_no_hidden_defect
  · simp [probabilityResidual]
    exact cover.shadowBounded
  · exact hcovers
  · exact hbudget

def finiteCoverOfSnowshoeSurface
    (surface : SnowshoeSurface) : FiniteCover :=
  { footprint := snowshoeFootprint surface.patches
    shadow := snowshoeShadow surface.patches
    horizon := surface.horizon
    footprintBounded := surface.footprintBounded
    shadowBounded := surface.shadowBounded }

theorem finite_cover_of_surface_shadow
    (surface : SnowshoeSurface) :
    (finiteCoverOfSnowshoeSurface surface).shadow =
      snowshoeShadow surface.patches := rfl

def finiteCoverOfCompletedInterface
    (interface : CompletedInfiniteInterface) : FiniteCover :=
  { footprint := interface.visibleDepth
    shadow := interface.shadow
    horizon := interface.horizon
    footprintBounded := completed_infinite_depth_within_horizon interface
    shadowBounded := completed_infinite_shadow_within_horizon interface }

theorem finite_cover_of_completed_interface_shadow
    (interface : CompletedInfiniteInterface) :
    (finiteCoverOfCompletedInterface interface).shadow =
      interface.shadow := rfl

structure FiniteCoverShrink where
  coarse : FiniteCover
  fine : FiniteCover
  savedShadow : Nat
  footprintGrowth : Nat
  shadowShrinks : fine.shadow + savedShadow = coarse.shadow
  footprintGrows : coarse.footprint + footprintGrowth = fine.footprint
  deriving Repr

theorem finite_cover_shrink_refines
    (certificate : FiniteCoverShrink)
    (hdepth :
      certificate.coarse.horizon.depth ≤ certificate.fine.horizon.depth)
    (hbudget :
      certificate.fine.horizon.residualBudget ≤
        certificate.coarse.horizon.residualBudget) :
    certificate.coarse.refines certificate.fine := by
  constructor
  · rw [← certificate.footprintGrows]
    exact Nat.le_add_right certificate.coarse.footprint
      certificate.footprintGrowth
  constructor
  · rw [← certificate.shadowShrinks]
    exact Nat.le_add_right certificate.fine.shadow
      certificate.savedShadow
  constructor
  · exact hdepth
  · exact hbudget

structure FiniteCoverExhaustion where
  cover : FiniteCover
  targetFootprint : Nat
  targetShadow : Nat
  footprintExact : cover.footprint = targetFootprint
  shadowExact : cover.shadow = targetShadow
  deriving Repr

theorem finite_cover_exhaustion_within_horizon
    (exhaustion : FiniteCoverExhaustion) :
    exhaustion.targetFootprint ≤ exhaustion.cover.horizon.depth ∧
      exhaustion.targetShadow ≤ exhaustion.cover.horizon.residualBudget := by
  constructor
  · rw [← exhaustion.footprintExact]
    exact exhaustion.cover.footprintBounded
  · rw [← exhaustion.shadowExact]
    exact exhaustion.cover.shadowBounded

theorem finite_cover_exhaustion_no_hidden_defect
    (exhaustion : FiniteCoverExhaustion)
    (wider : Nat)
    (observer : ScalarObserver)
    (depth : Nat)
    (hcovers :
      ObserverBudgetCovers natBudgetMeasure
        exhaustion.cover.horizon.residualBudget wider)
    (hbudget : wider ≤ depth) :
    natResidualSignature.answer
      (probabilityObserverPromotion.promote
        { unobservedMass := exhaustion.targetShadow,
          truncatedMass := 0,
          coarseningDebt := 0 } ())
      observer depth := by
  apply probability_no_hidden_defect
  · simp [probabilityResidual]
    exact (finite_cover_exhaustion_within_horizon exhaustion).2
  · exact hcovers
  · exact hbudget

def finiteCoverExhaustionOfSurface
    (exhaustion : FiniteSurfaceExhaustion) : FiniteCoverExhaustion :=
  { cover := finiteCoverOfSnowshoeSurface exhaustion.surface
    targetFootprint := exhaustion.interface.visibleDepth
    targetShadow := exhaustion.interface.shadow
    footprintExact := by
      rw [finite_surface_exhaustion_depth_eq_surface]
      rfl
    shadowExact := by
      rw [finite_surface_exhaustion_shadow_eq_surface]
      rfl }

theorem finite_cover_exhaustion_of_surface_shadow
    (exhaustion : FiniteSurfaceExhaustion) :
    (finiteCoverExhaustionOfSurface exhaustion).targetShadow =
      exhaustion.interface.shadow := rfl

def finiteCoverOfProcessChain
    (chain : FiniteProbabilityProcessChain)
    (horizon : FiniteHorizon)
    (hfootprint : chain.output.totalMass ≤ horizon.depth)
    (hshadow : chain.residual ≤ horizon.residualBudget) :
    FiniteCover :=
  { footprint := chain.output.totalMass
    shadow := chain.residual
    horizon := horizon
    footprintBounded := hfootprint
    shadowBounded := hshadow }

theorem finite_cover_of_process_chain_shadow
    (chain : FiniteProbabilityProcessChain)
    (horizon : FiniteHorizon)
    (hfootprint : chain.output.totalMass ≤ horizon.depth)
    (hshadow : chain.residual ≤ horizon.residualBudget) :
    (finiteCoverOfProcessChain chain horizon hfootprint hshadow).shadow =
      chain.residual := rfl

def finiteCoverOfMarkovWitness
    (witness : FiniteMarkovWitness)
    (horizon : FiniteHorizon)
    (footprint : Nat)
    (hfootprint : footprint ≤ horizon.depth)
    (hshadow : witness.totalShadow ≤ horizon.residualBudget) :
    FiniteCover :=
  { footprint := footprint
    shadow := witness.totalShadow
    horizon := horizon
    footprintBounded := hfootprint
    shadowBounded := hshadow }

theorem finite_cover_of_markov_witness_shadow
    (witness : FiniteMarkovWitness)
    (horizon : FiniteHorizon)
    (footprint : Nat)
    (hfootprint : footprint ≤ horizon.depth)
    (hshadow : witness.totalShadow ≤ horizon.residualBudget) :
    (finiteCoverOfMarkovWitness
      witness horizon footprint hfootprint hshadow).shadow =
        witness.totalShadow := rfl

end FiniteProbabilityCore
end Gnosis
