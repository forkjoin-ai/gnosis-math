import Gnosis.GodFormula
import Gnosis.HeraclesTwelveLaborsWitness
import Gnosis.SpectralNoiseEquilibrium

namespace Gnosis
namespace HeraclesLaborTransitionGraphWitness

open SpectralNoiseEquilibrium
open HeraclesTwelveLaborsWitness

/-!
# Heracles Labor Transition Graph Witness

Directed transition graph for the twelve-labor debugging pipeline.  The
exhaustive Heracles suite proves each filter independently; this file proves
the order-sensitive path from substrate hardening through void-boundary
integration.
-/

def laborIndex : LaborTest → Nat
  | .nemeanLion => 1
  | .hydra => 2
  | .ceryneianHind => 3
  | .erymanthianBoar => 4
  | .augeanStables => 5
  | .stymphalianBirds => 6
  | .cretanBull => 7
  | .maresOfDiomedes => 8
  | .beltOfHippolyta => 9
  | .cattleOfGeryon => 10
  | .applesOfHesperides => 11
  | .cerberus => 12

def laborTransition (a b : LaborTest) : Prop :=
  laborIndex b = laborIndex a + 1

def canonicalLaborPath : List LaborTest :=
  [ .nemeanLion
  , .hydra
  , .ceryneianHind
  , .erymanthianBoar
  , .augeanStables
  , .stymphalianBirds
  , .cretanBull
  , .maresOfDiomedes
  , .beltOfHippolyta
  , .cattleOfGeryon
  , .applesOfHesperides
  , .cerberus
  ]

def pathLength : Nat :=
  canonicalLaborPath.length

def transitionCount : Nat :=
  pathLength - 1

structure PipelineEndpoints where
  startsAtSubstrateHardening : Bool
  endsAtVoidBoundaryIntegration : Bool
deriving Repr, DecidableEq

def heraclesPipelineEndpoints : PipelineEndpoints :=
  { startsAtSubstrateHardening := true
    endsAtVoidBoundaryIntegration := true }

def orderedDebuggingPipeline (p : PipelineEndpoints) : Prop :=
  p.startsAtSubstrateHardening = true ∧
    p.endsAtVoidBoundaryIntegration = true

def transitionGraphCost : BuleyUnit :=
  { waste := 3, opportunity := 4, diversity := 5 }

def transitionGraphFloorWeight : Nat :=
  godWeight transitionGraphCost.diversity transitionGraphCost.diversity

theorem transition_lion_to_hydra :
    laborTransition .nemeanLion .hydra := by
  unfold laborTransition laborIndex
  rfl

theorem transition_hydra_to_hind :
    laborTransition .hydra .ceryneianHind := by
  unfold laborTransition laborIndex
  rfl

theorem transition_hind_to_boar :
    laborTransition .ceryneianHind .erymanthianBoar := by
  unfold laborTransition laborIndex
  rfl

theorem transition_boar_to_stables :
    laborTransition .erymanthianBoar .augeanStables := by
  unfold laborTransition laborIndex
  rfl

theorem transition_stables_to_birds :
    laborTransition .augeanStables .stymphalianBirds := by
  unfold laborTransition laborIndex
  rfl

theorem transition_birds_to_bull :
    laborTransition .stymphalianBirds .cretanBull := by
  unfold laborTransition laborIndex
  rfl

theorem transition_bull_to_mares :
    laborTransition .cretanBull .maresOfDiomedes := by
  unfold laborTransition laborIndex
  rfl

theorem transition_mares_to_belt :
    laborTransition .maresOfDiomedes .beltOfHippolyta := by
  unfold laborTransition laborIndex
  rfl

theorem transition_belt_to_cattle :
    laborTransition .beltOfHippolyta .cattleOfGeryon := by
  unfold laborTransition laborIndex
  rfl

theorem transition_cattle_to_apples :
    laborTransition .cattleOfGeryon .applesOfHesperides := by
  unfold laborTransition laborIndex
  rfl

theorem transition_apples_to_cerberus :
    laborTransition .applesOfHesperides .cerberus := by
  unfold laborTransition laborIndex
  rfl

theorem canonical_path_has_twelve_nodes :
    pathLength = 12 := by
  unfold pathLength canonicalLaborPath
  rfl

theorem canonical_path_has_eleven_edges :
    transitionCount = 11 := by
  unfold transitionCount
  rw [canonical_path_has_twelve_nodes]

theorem pipeline_endpoints_are_ordered :
    orderedDebuggingPipeline heraclesPipelineEndpoints := by
  unfold orderedDebuggingPipeline heraclesPipelineEndpoints
  exact ⟨rfl, rfl⟩

theorem transition_graph_cost_is_twelve :
    buleyUnitScore transitionGraphCost = 12 := by
  unfold transitionGraphCost buleyUnitScore
  decide

theorem transition_graph_floor_weight_is_unit :
    transitionGraphFloorWeight = 1 := by
  unfold transitionGraphFloorWeight transitionGraphCost
  exact godWeight_floor 5

theorem heracles_labor_transition_graph_witness :
    pathLength = 12 ∧
    transitionCount = 11 ∧
    laborTransition .nemeanLion .hydra ∧
    laborTransition .hydra .ceryneianHind ∧
    laborTransition .ceryneianHind .erymanthianBoar ∧
    laborTransition .erymanthianBoar .augeanStables ∧
    laborTransition .augeanStables .stymphalianBirds ∧
    laborTransition .stymphalianBirds .cretanBull ∧
    laborTransition .cretanBull .maresOfDiomedes ∧
    laborTransition .maresOfDiomedes .beltOfHippolyta ∧
    laborTransition .beltOfHippolyta .cattleOfGeryon ∧
    laborTransition .cattleOfGeryon .applesOfHesperides ∧
    laborTransition .applesOfHesperides .cerberus ∧
    orderedDebuggingPipeline heraclesPipelineEndpoints ∧
    buleyUnitScore transitionGraphCost = 12 ∧
    transitionGraphFloorWeight = 1 := by
  exact ⟨canonical_path_has_twelve_nodes,
    canonical_path_has_eleven_edges,
    transition_lion_to_hydra,
    transition_hydra_to_hind,
    transition_hind_to_boar,
    transition_boar_to_stables,
    transition_stables_to_birds,
    transition_birds_to_bull,
    transition_bull_to_mares,
    transition_mares_to_belt,
    transition_belt_to_cattle,
    transition_cattle_to_apples,
    transition_apples_to_cerberus,
    pipeline_endpoints_are_ordered,
    transition_graph_cost_is_twelve,
    transition_graph_floor_weight_is_unit⟩

end HeraclesLaborTransitionGraphWitness
end Gnosis
