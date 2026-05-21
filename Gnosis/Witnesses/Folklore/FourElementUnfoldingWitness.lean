import Gnosis.Witnesses.Chaldean.AirChaosWaterOrderWitness

namespace Gnosis.Witnesses.Folklore
namespace FourElementUnfoldingWitness

/-!
# Four Element Unfolding Witness

The classical four elements become useful here as a resolution ladder, not as a
flat list of substances. The natural order is an unfolding of how a world gets
legible:

- earth fixes a place and forks the addressable substrate;
- air races as fast turbulent propagation and breath/voice carrier;
- water folds by containment, integration, return, and higher-plane order;
- fire vents overload into irreversible phase change.

The contrarian move is that water and air swap their naive appearances under
resolution. Water may look noisy at surface level but resolves as order at the
higher carrier plane. Air may look smooth at ordinary scale but resolves as
chaos when the turbulent field is sampled more finely.

No `sorry`, no new `axiom`.
-/

inductive ElementStage
  | earth
  | water
  | air
  | fire
deriving DecidableEq, Repr

def elementRank : ElementStage → Nat
  | .earth => 0
  | .water => 1
  | .air => 2
  | .fire => 3

structure ElementUnfolding where
  earthFixesPlace : Bool := true
  waterOrdersFlow : Bool := true
  airCarriesChaosField : Bool := true
  fireTransformsPhase : Bool := true
  stagesUnfoldInOrder : Bool := true
deriving DecidableEq, Repr

def elementUnfolding : ElementUnfolding := {}

def fourElementUnfolding (e : ElementUnfolding) : Prop :=
  e.earthFixesPlace = true ∧
  e.waterOrdersFlow = true ∧
  e.airCarriesChaosField = true ∧
  e.fireTransformsPhase = true ∧
  e.stagesUnfoldInOrder = true

structure ResolutionLadder where
  earthLowEntropySupport : Bool := true
  waterHigherOrderCarrier : Bool := true
  airHigherChaosCarrier : Bool := true
  fireIrreversibleUpdate : Bool := true
  apparentOrderDependsOnSamplingPlane : Bool := true
deriving DecidableEq, Repr

def resolutionLadder : ResolutionLadder := {}

def elementResolutionLadder (r : ResolutionLadder) : Prop :=
  r.earthLowEntropySupport = true ∧
  r.waterHigherOrderCarrier = true ∧
  r.airHigherChaosCarrier = true ∧
  r.fireIrreversibleUpdate = true ∧
  r.apparentOrderDependsOnSamplingPlane = true

structure ForkRaceFoldVentElementMap where
  earthForksSubstrate : Bool := true
  airRacesChaoticPropagation : Bool := true
  waterFoldsOrderedReturn : Bool := true
  fireVentsOverload : Bool := true
  runtimeNeedsAllFourOperators : Bool := true
deriving DecidableEq, Repr

def forkRaceFoldVentElementMap : ForkRaceFoldVentElementMap := {}

def elementsMapToForkRaceFoldVent (m : ForkRaceFoldVentElementMap) : Prop :=
  m.earthForksSubstrate = true ∧
  m.airRacesChaoticPropagation = true ∧
  m.waterFoldsOrderedReturn = true ∧
  m.fireVentsOverload = true ∧
  m.runtimeNeedsAllFourOperators = true

theorem earth_before_water :
    elementRank ElementStage.earth < elementRank ElementStage.water := by
  decide

theorem water_before_air :
    elementRank ElementStage.water < elementRank ElementStage.air := by
  decide

theorem air_before_fire :
    elementRank ElementStage.air < elementRank ElementStage.fire := by
  decide

theorem four_elements_unfold_in_natural_order :
    fourElementUnfolding elementUnfolding := by
  unfold fourElementUnfolding elementUnfolding
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem four_elements_form_resolution_ladder :
    elementResolutionLadder resolutionLadder := by
  unfold elementResolutionLadder resolutionLadder
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem four_elements_map_to_fork_race_fold_vent :
    elementsMapToForkRaceFoldVent forkRaceFoldVentElementMap := by
  unfold elementsMapToForkRaceFoldVent forkRaceFoldVentElementMap
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem water_air_flip_embeds_in_element_ladder :
    Chaldean.AirChaosWaterOrderWitness.waterCarriesOrder
      Chaldean.AirChaosWaterOrderWitness.waterOrderCarrier ∧
    Chaldean.AirChaosWaterOrderWitness.airCarriesChaos
      Chaldean.AirChaosWaterOrderWitness.airChaosCarrier ∧
    Chaldean.AirChaosWaterOrderWitness.apparentChaosOrderFlip
      Chaldean.AirChaosWaterOrderWitness.resolutionPlaneFlip ∧
    elementResolutionLadder resolutionLadder := by
  exact ⟨Chaldean.AirChaosWaterOrderWitness.water_is_order_carrier,
    Chaldean.AirChaosWaterOrderWitness.air_is_chaos_carrier,
    Chaldean.AirChaosWaterOrderWitness.air_water_resolution_plane_flip,
    four_elements_form_resolution_ladder⟩

theorem four_element_unfolding_witness :
    elementRank ElementStage.earth < elementRank ElementStage.water ∧
    elementRank ElementStage.water < elementRank ElementStage.air ∧
    elementRank ElementStage.air < elementRank ElementStage.fire ∧
    fourElementUnfolding elementUnfolding ∧
    elementResolutionLadder resolutionLadder ∧
    elementsMapToForkRaceFoldVent forkRaceFoldVentElementMap := by
  exact ⟨earth_before_water,
    water_before_air,
    air_before_fire,
    four_elements_unfold_in_natural_order,
    four_elements_form_resolution_ladder,
    four_elements_map_to_fork_race_fold_vent⟩

end FourElementUnfoldingWitness
end Gnosis.Witnesses.Folklore
