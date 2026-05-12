import Init

/-!
# Physarum Flux Routing Witnesses

Finite Init witnesses for a pushed Physarum model: tube thickness is
state-bearing memory, routing follows reliable flux rather than shortest-path
alone, and the same local update can be evaluated on several ambient surfaces.
-/

namespace Gnosis.PhysarumFluxRouting

inductive Tube where
  | ab | bc | ac | cd | bypass
deriving DecidableEq, Repr

structure TubeState where
  thickness : Nat
  flow : Nat
deriving Repr, DecidableEq

def updateTube (state : TubeState) : TubeState :=
  if state.flow = 0 then
    { state with thickness := state.thickness - 1 }
  else
    { state with thickness := state.thickness + state.flow }

theorem active_flow_thickens_tube :
    (updateTube { thickness := 3, flow := 2 }).thickness = 5 := by
  native_decide

theorem zero_flow_prunes_tube :
    (updateTube { thickness := 3, flow := 0 }).thickness = 2 := by
  native_decide

theorem tube_update_is_memristive :
    (updateTube { thickness := 3, flow := 2 }).thickness ≠
      (updateTube { thickness := 3, flow := 0 }).thickness := by
  native_decide

structure NetworkDesign where
  totalLength : Nat
  averagePathLength : Nat
  faultTolerance : Nat
deriving Repr, DecidableEq

def shortestTree : NetworkDesign :=
  { totalLength := 5, averagePathLength := 6, faultTolerance := 1 }

def fastCore : NetworkDesign :=
  { totalLength := 7, averagePathLength := 3, faultTolerance := 2 }

def redundantPhysarum : NetworkDesign :=
  { totalLength := 8, averagePathLength := 4, faultTolerance := 4 }

def dominates (x y : NetworkDesign) : Bool :=
  x.totalLength ≤ y.totalLength &&
    x.averagePathLength ≤ y.averagePathLength &&
    y.faultTolerance ≤ x.faultTolerance &&
    (x.totalLength < y.totalLength ||
      x.averagePathLength < y.averagePathLength ||
      y.faultTolerance < x.faultTolerance)

theorem shortest_tree_does_not_dominate_physarum :
    dominates shortestTree redundantPhysarum = false := by
  native_decide

theorem fast_core_does_not_dominate_physarum :
    dominates fastCore redundantPhysarum = false := by
  native_decide

theorem physarum_does_not_dominate_shortest_tree :
    dominates redundantPhysarum shortestTree = false := by
  native_decide

theorem physarum_tradeoff_is_pareto_visible :
    dominates shortestTree redundantPhysarum = false ∧
    dominates fastCore redundantPhysarum = false ∧
    dominates redundantPhysarum shortestTree = false := by
  native_decide

structure Route where
  distance : Nat
  fluxReliability : Nat
  backpressure : Nat
deriving Repr, DecidableEq

def shortestFragileRoute : Route :=
  { distance := 3, fluxReliability := 2, backpressure := 5 }

def reliableFluxRoute : Route :=
  { distance := 4, fluxReliability := 7, backpressure := 2 }

def routeScore (route : Route) : Nat :=
  route.fluxReliability * 10 - route.backpressure

theorem reliable_flux_beats_shortest_fragile_route :
    routeScore shortestFragileRoute < routeScore reliableFluxRoute := by
  native_decide

inductive Surface where
  | disk | torus | mobius
deriving DecidableEq, Repr

def localRuleInvariant (_surface : Surface) (state : TubeState) : Nat :=
  (updateTube state).thickness

theorem local_update_same_on_disk_and_torus :
    localRuleInvariant .disk { thickness := 3, flow := 2 } =
      localRuleInvariant .torus { thickness := 3, flow := 2 } := by
  native_decide

theorem local_update_same_on_mobius_and_disk :
    localRuleInvariant .mobius { thickness := 3, flow := 0 } =
      localRuleInvariant .disk { thickness := 3, flow := 0 } := by
  native_decide

theorem physarum_flux_summary :
    (updateTube { thickness := 3, flow := 2 }).thickness = 5 ∧
    (updateTube { thickness := 3, flow := 0 }).thickness = 2 ∧
    routeScore shortestFragileRoute < routeScore reliableFluxRoute ∧
    localRuleInvariant .disk { thickness := 3, flow := 2 } =
      localRuleInvariant .torus { thickness := 3, flow := 2 } := by
  native_decide

end Gnosis.PhysarumFluxRouting
