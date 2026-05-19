import Gnosis.CrossDomain.CrossDomainQueueingMycologyEntanglement
import Gnosis.TopologicalGrassmannianCompiler

/-!
# Mycelial Topological Ordering

Finite scheduler certificate for the Aeon Sorts pivot from scalar total-order
sorting to topology-aware work ordering. The point is deliberately small:
dependency preservation, route-cost admissibility, and mycelial capacity
dominance are separate obligations that can be checked before runtime
benchmarks claim speed.
-/

namespace Gnosis

open Gnosis.GrassmannianCompiler

structure MycelialWorkGraph where
  nodes : Nat
  edges : Nat
deriving DecidableEq, Repr

structure MycelialOrderingWitness where
  graph : MycelialWorkGraph
  dependencyPreserved : Prop
  routeCost : Nat
  nutrientCost : Nat
  peakBacklog : Nat
  corridorCapacity : Nat
  foldDebt : Nat
deriving Repr

structure MycelialProjectionCacheWitness where
  witness : MycelialOrderingWitness
  fingerprintStable : Prop
  cacheHit : Prop
deriving Repr

structure MycelialProjectionFeature where
  route : Nat
  nutrient : Nat
  inDegree : Nat
  outDegree : Nat
  inputHint : Nat
  node : Nat
deriving DecidableEq, Repr

def natAbsDiff (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

def pluckerMinorNat (aᵢ aⱼ bᵢ bⱼ : Nat) : Nat :=
  natAbsDiff aᵢ aⱼ +
  natAbsDiff bᵢ bⱼ +
  natAbsDiff (aᵢ * bⱼ) (aⱼ * bᵢ)

def mycelialPluckerCoordinate (feature : MycelialProjectionFeature) : Nat :=
  let rowA0 := feature.route + 1
  let rowA1 := feature.nutrient + 1
  let rowA2 := feature.inputHint + 1
  let rowA3 := feature.node + 1
  let rowB0 := feature.outDegree + 1
  let rowB1 := feature.inDegree + 1
  let rowB2 := feature.route + feature.nutrient + 1
  let rowB3 := feature.inputHint + feature.node + 1
  3 * pluckerMinorNat rowA0 rowA1 rowB0 rowB1 +
  5 * pluckerMinorNat rowA0 rowA2 rowB0 rowB2 +
  7 * pluckerMinorNat rowA1 rowA3 rowB1 rowB3

def mycelialPluckerCorridor
    (feature : MycelialProjectionFeature)
    (corridorCount : Nat) : Nat :=
  if corridorCount = 0 then 0 else mycelialPluckerCoordinate feature % corridorCount

theorem mycelial_plucker_corridor_lt
    (feature : MycelialProjectionFeature)
    (corridorCount : Nat)
    (hPositive : corridorCount > 0) :
    mycelialPluckerCorridor feature corridorCount < corridorCount := by
  unfold mycelialPluckerCorridor
  split
  · subst corridorCount
    exact False.elim (Nat.lt_irrefl 0 hPositive)
  · exact Nat.mod_lt _ hPositive

def fifoQueueCapacity (graph : MycelialWorkGraph) : Nat :=
  queue_capacity graph.nodes

def mycelialOrderingCapacity (graph : MycelialWorkGraph) : Nat :=
  mycelial_network_capacity graph.nodes

def mycelialRouteAdmissible (witness : MycelialOrderingWitness) : Prop :=
  witness.routeCost ≤ witness.nutrientCost

def mycelialScheduleValid (witness : MycelialOrderingWitness) : Prop :=
  witness.dependencyPreserved ∧
  mycelialRouteAdmissible witness ∧
  witness.peakBacklog ≤ witness.corridorCapacity ∧
  witness.corridorCapacity ≤ mycelialOrderingCapacity witness.graph ∧
  witness.foldDebt ≤ witness.graph.edges

theorem mycelial_ordering_capacity_dominates_fifo
    (graph : MycelialWorkGraph)
    (hNodes : graph.nodes > 0) :
    fifoQueueCapacity graph < mycelialOrderingCapacity graph := by
  unfold fifoQueueCapacity mycelialOrderingCapacity
  exact mycology_dominates_queueing graph.nodes hNodes

theorem mycelial_ordering_valid_preserves_dependencies
    (witness : MycelialOrderingWitness)
    (hValid : mycelialScheduleValid witness) :
    witness.dependencyPreserved := by
  exact hValid.1

theorem mycelial_ordering_valid_bounds_route_cost
    (witness : MycelialOrderingWitness)
    (hValid : mycelialScheduleValid witness) :
    witness.routeCost ≤ witness.nutrientCost := by
  exact hValid.2.1

theorem mycelial_ordering_valid_bounds_peak_backlog
    (witness : MycelialOrderingWitness)
    (hValid : mycelialScheduleValid witness) :
    witness.peakBacklog ≤ witness.corridorCapacity := by
  exact hValid.2.2.1

theorem mycelial_ordering_valid_corridor_capacity_within_network
    (witness : MycelialOrderingWitness)
    (hValid : mycelialScheduleValid witness) :
    witness.corridorCapacity ≤ mycelialOrderingCapacity witness.graph := by
  exact hValid.2.2.2.1

theorem mycelial_ordering_valid_bounds_peak_backlog_by_network
    (witness : MycelialOrderingWitness)
    (hValid : mycelialScheduleValid witness) :
    witness.peakBacklog ≤ mycelialOrderingCapacity witness.graph := by
  exact Nat.le_trans
    (mycelial_ordering_valid_bounds_peak_backlog witness hValid)
    (mycelial_ordering_valid_corridor_capacity_within_network witness hValid)

theorem mycelial_ordering_valid_bounds_fold_debt
    (witness : MycelialOrderingWitness)
    (hValid : mycelialScheduleValid witness) :
    witness.foldDebt ≤ witness.graph.edges := by
  exact hValid.2.2.2.2

theorem mycelial_ordering_beats_fifo_when_valid_and_positive
    (witness : MycelialOrderingWitness)
    (hNodes : witness.graph.nodes > 0)
    (hValid : mycelialScheduleValid witness) :
    witness.dependencyPreserved ∧
    witness.routeCost ≤ witness.nutrientCost ∧
    witness.peakBacklog ≤ witness.corridorCapacity ∧
    witness.peakBacklog ≤ mycelialOrderingCapacity witness.graph ∧
    fifoQueueCapacity witness.graph < mycelialOrderingCapacity witness.graph := by
  exact ⟨
    mycelial_ordering_valid_preserves_dependencies witness hValid,
    mycelial_ordering_valid_bounds_route_cost witness hValid,
    mycelial_ordering_valid_bounds_peak_backlog witness hValid,
    mycelial_ordering_valid_bounds_peak_backlog_by_network witness hValid,
    mycelial_ordering_capacity_dominates_fifo witness.graph hNodes
  ⟩

def mycelialGrassmannianPlane
    (witness : MycelialOrderingWitness)
    (hCorridor : witness.corridorCapacity > 0) :
    CFGTopology 2 witness.graph.nodes :=
  { states := witness.graph.nodes,
    constraints := witness.corridorCapacity,
    is_positive := hCorridor }

def projectedMycelialGrassmannian
    (witness : MycelialOrderingWitness)
    (hCorridor : witness.corridorCapacity > 0) :
    PositiveGrassmannian 2 witness.graph.nodes :=
  compile_cfg_to_grassmannian
    (mycelialGrassmannianPlane witness hCorridor)

theorem mycelial_grassmannian_projection_volume
    (witness : MycelialOrderingWitness)
    (hCorridor : witness.corridorCapacity > 0) :
    (projectedMycelialGrassmannian witness hCorridor).volume =
      witness.graph.nodes * witness.corridorCapacity := by
  rfl

theorem valid_mycelial_schedule_survives_grassmannian_projection
    (witness : MycelialOrderingWitness)
    (hCorridor : witness.corridorCapacity > 0)
    (hValid : mycelialScheduleValid witness) :
    witness.dependencyPreserved ∧
    witness.routeCost ≤ witness.nutrientCost ∧
    witness.peakBacklog ≤ witness.corridorCapacity ∧
    (projectedMycelialGrassmannian witness hCorridor).volume =
      witness.graph.nodes * witness.corridorCapacity := by
  exact ⟨
    mycelial_ordering_valid_preserves_dependencies witness hValid,
    mycelial_ordering_valid_bounds_route_cost witness hValid,
    mycelial_ordering_valid_bounds_peak_backlog witness hValid,
    mycelial_grassmannian_projection_volume witness hCorridor
  ⟩

def mycelialProjectionCacheValid
    (cached : MycelialProjectionCacheWitness) : Prop :=
  cached.fingerprintStable ∧ cached.cacheHit ∧
  mycelialScheduleValid cached.witness

theorem cached_projection_preserves_valid_schedule
    (cached : MycelialProjectionCacheWitness)
    (hValid : mycelialProjectionCacheValid cached) :
    mycelialScheduleValid cached.witness := by
  exact hValid.2.2

theorem cached_projection_preserves_grassmannian_volume
    (cached : MycelialProjectionCacheWitness)
    (hCorridor : cached.witness.corridorCapacity > 0)
    (_hValid : mycelialProjectionCacheValid cached) :
    (projectedMycelialGrassmannian cached.witness hCorridor).volume =
      cached.witness.graph.nodes * cached.witness.corridorCapacity := by
  exact mycelial_grassmannian_projection_volume cached.witness hCorridor

end Gnosis
