import Gnosis.JacksonQueueing
import Gnosis.PhysarumRopelength
import Gnosis.CrossDomain.CrossDomainQueueingMycologyEntanglement
import Gnosis.GeometricErgodicity

/-!
# Anarchy games as Jackson queue control tradeoffs

This module ties the anarchy/control game surface in
`PhysarumRopelength.lean` to the finite Jackson queue data shape in
`JacksonQueueing.lean`.

The bridge is intentionally discrete. Control pressure is not treated as free
coordination; it enters as queue load. Healthy anarchy wins when distributed
service and shared boundary signals cover the control load. Command-control
and total-anarchy saturation are both shown as positive-backlog regimes in this
finite model.
-/

namespace Gnosis
namespace AnarchyJacksonQueueBridge

open Gnosis.PhysarumRopelength

/-- Two-node Jackson sketch: local work plus coordination/control work. -/
inductive AnarchyQueueNode where
  | localWork
  | controlWork
deriving DecidableEq, Repr

/--
Queue load induced by an anarchy equilibrium.

`organicArrival` is the unavoidable local work. `controlArrival` is extra
queue load caused by centralized pressure and redundant agreement pressure.
`serviceCapacity` is the distributed service available from local agents and
shared boundary signals.
-/
structure AnarchyQueueLoad where
  organicArrival : Nat
  controlArrival : Nat
  serviceCapacity : Nat
deriving Repr, DecidableEq

/-- Control pressure contributes as queue arrival, not as free throughput. -/
def controlArrival (equilibrium : AnarchyEquilibrium) : Nat :=
  standingWaveControlPressure equilibrium +
    redundantAgreementPressure equilibrium

/-- Distributed service capacity available to absorb local/control load. -/
def serviceCapacity (equilibrium : AnarchyEquilibrium) : Nat :=
  equilibrium.localAgents + equilibrium.sharedBoundarySignals

/-- Read an anarchy equilibrium as a finite queue-load witness. -/
def queueLoadOfAnarchy (equilibrium : AnarchyEquilibrium) :
    AnarchyQueueLoad :=
  { organicArrival := equilibrium.populationSize,
    controlArrival := controlArrival equilibrium,
    serviceCapacity := serviceCapacity equilibrium }

/-- Total arrival into the control queue sketch. -/
def totalArrival (load : AnarchyQueueLoad) : Nat :=
  load.organicArrival + load.controlArrival

/-- Saturating backlog: the Jackson-side residual after service. -/
def jacksonBacklog (load : AnarchyQueueLoad) : Nat :=
  totalArrival load - load.serviceCapacity

/-- Saturating backlog under an explicitly supplied service capacity. -/
def backlogWithService (load : AnarchyQueueLoad) (service : Nat) : Nat :=
  totalArrival load - service

/-- Increasing service capacity cannot increase residual queue backlog. -/
theorem backlog_antitone_in_service
    (load : AnarchyQueueLoad) {service₁ service₂ : Nat}
    (hService : service₁ ≤ service₂) :
    backlogWithService load service₂ ≤ backlogWithService load service₁ := by
  unfold backlogWithService
  exact Nat.sub_le_sub_left hService (totalArrival load)

/-- If service covers total arrival, residual backlog is zero. -/
theorem backlog_with_service_zero_when_service_covers
    (load : AnarchyQueueLoad) {service : Nat}
    (hCover : totalArrival load ≤ service) :
    backlogWithService load service = 0 := by
  unfold backlogWithService
  exact Nat.sub_eq_zero_of_le hCover

/-- The original Jackson backlog is the explicit-service backlog at `load.serviceCapacity`. -/
theorem jackson_backlog_eq_backlog_with_native_service
    (load : AnarchyQueueLoad) :
    jacksonBacklog load = backlogWithService load load.serviceCapacity := rfl

/-- Stable control queue: service covers organic plus control arrivals. -/
def JacksonControlStable (load : AnarchyQueueLoad) : Prop :=
  totalArrival load ≤ load.serviceCapacity

/-- If a load is Jackson-stable, its backlog is zero. -/
theorem stable_control_queue_has_zero_backlog
    {load : AnarchyQueueLoad} (h : JacksonControlStable load) :
    jacksonBacklog load = 0 := by
  unfold JacksonControlStable at h
  unfold jacksonBacklog
  exact Nat.sub_eq_zero_of_le h

/-- Zero backlog recovers the Jackson stability inequality. -/
theorem zero_backlog_iff_jackson_control_stable
    (load : AnarchyQueueLoad) :
    jacksonBacklog load = 0 ↔ JacksonControlStable load := by
  constructor
  · intro h
    unfold jacksonBacklog at h
    unfold JacksonControlStable
    exact Nat.le_of_sub_eq_zero h
  · intro h
    exact stable_control_queue_has_zero_backlog h

/-- Turn an anarchy equilibrium into the repository's Jackson traffic shape. -/
def jacksonTrafficOfAnarchy (equilibrium : AnarchyEquilibrium) :
    JacksonTrafficData AnarchyQueueNode :=
  { externalArrival := fun
      | .localWork => equilibrium.populationSize
      | .controlWork => controlArrival equilibrium,
    routing := fun
      | .localWork, .controlWork => redundantAgreementPressure equilibrium
      | _, _ => 0,
    serviceRate := fun
      | .localWork => equilibrium.localAgents
      | .controlWork => serviceCapacity equilibrium }

/-- Human Jackson queue theory reads service as the finite local service count. -/
def humanJacksonServiceCapacity (nodes : Nat) : Nat :=
  queue_capacity nodes

/-- Mycelium reads the same node count through a denser adaptive network. -/
def mycelialServiceCapacity (nodes : Nat) : Nat :=
  mycelial_network_capacity nodes

/--
Mycelium strictly dominates the human queue-theory capacity model on every
positive node count, reusing the cross-domain mycology/queueing theorem.
-/
theorem mycelium_strictly_dominates_human_queue_capacity
    (nodes : Nat) (hNodes : 0 < nodes) :
    humanJacksonServiceCapacity nodes < mycelialServiceCapacity nodes := by
  unfold humanJacksonServiceCapacity mycelialServiceCapacity
  exact mycology_dominates_queueing nodes hNodes

/-- Healthy anarchy has a positive distributed node count. -/
theorem healthy_anarchy_positive_node_count :
    0 < serviceCapacity distributedAnarchyEquilibrium := by
  unfold serviceCapacity distributedAnarchyEquilibrium
  native_decide

/--
At healthy-anarchy scale, mycelial routing strictly dominates the human
Jackson reading of the same service node count.
-/
theorem healthy_anarchy_mycelium_dominates_human_queue_service :
    humanJacksonServiceCapacity
        (serviceCapacity distributedAnarchyEquilibrium) <
      mycelialServiceCapacity
        (serviceCapacity distributedAnarchyEquilibrium) :=
  mycelium_strictly_dominates_human_queue_capacity
    (serviceCapacity distributedAnarchyEquilibrium)
    healthy_anarchy_positive_node_count

/-- Human service reading for a load at a chosen node count. -/
def humanBacklogForNodes (load : AnarchyQueueLoad) (nodes : Nat) : Nat :=
  backlogWithService load (humanJacksonServiceCapacity nodes)

/-- Mycelial service reading for the same load and node count. -/
def mycelialBacklogForNodes (load : AnarchyQueueLoad) (nodes : Nat) : Nat :=
  backlogWithService load (mycelialServiceCapacity nodes)

/--
For the same arrival load and positive node count, mycelial service weakly
lowers the residual backlog against the human Jackson service reading.
-/
theorem mycelial_service_weakly_lowers_backlog
    (load : AnarchyQueueLoad) (nodes : Nat) (hNodes : 0 < nodes) :
    mycelialBacklogForNodes load nodes ≤ humanBacklogForNodes load nodes := by
  unfold mycelialBacklogForNodes humanBacklogForNodes
  exact backlog_antitone_in_service load
    (Nat.le_of_lt (mycelium_strictly_dominates_human_queue_capacity nodes hNodes))

/-- If mycelial service covers the load, the mycelial residual backlog is zero. -/
theorem mycelial_backlog_zero_when_service_covers
    (load : AnarchyQueueLoad) (nodes : Nat)
    (hCover : totalArrival load ≤ mycelialServiceCapacity nodes) :
    mycelialBacklogForNodes load nodes = 0 := by
  unfold mycelialBacklogForNodes
  exact backlog_with_service_zero_when_service_covers load hCover

/-- At healthy-anarchy node count, mycelial service weakly lowers the same-load backlog. -/
theorem healthy_anarchy_mycelial_service_weakly_lowers_backlog :
    mycelialBacklogForNodes
        (queueLoadOfAnarchy distributedAnarchyEquilibrium)
        (serviceCapacity distributedAnarchyEquilibrium) ≤
      humanBacklogForNodes
        (queueLoadOfAnarchy distributedAnarchyEquilibrium)
        (serviceCapacity distributedAnarchyEquilibrium) :=
  mycelial_service_weakly_lowers_backlog
    (queueLoadOfAnarchy distributedAnarchyEquilibrium)
    (serviceCapacity distributedAnarchyEquilibrium)
    healthy_anarchy_positive_node_count

/-- Healthy-anarchy mycelial service covers the same control load outright. -/
theorem healthy_anarchy_mycelial_service_covers_load :
    totalArrival (queueLoadOfAnarchy distributedAnarchyEquilibrium) ≤
      mycelialServiceCapacity (serviceCapacity distributedAnarchyEquilibrium) := by
  unfold totalArrival
    queueLoadOfAnarchy
    controlArrival
    serviceCapacity
    mycelialServiceCapacity
    mycelial_network_capacity
    distributedAnarchyEquilibrium
    standingWaveControlPressure
    redundantAgreementPressure
    centralizationPressure
    distributedAntPhysarum
  native_decide

/-- Healthy-anarchy mycelial service clears the same-load backlog. -/
theorem healthy_anarchy_mycelial_backlog_zero :
    mycelialBacklogForNodes
        (queueLoadOfAnarchy distributedAnarchyEquilibrium)
        (serviceCapacity distributedAnarchyEquilibrium) = 0 :=
  mycelial_backlog_zero_when_service_covers
    (queueLoadOfAnarchy distributedAnarchyEquilibrium)
    (serviceCapacity distributedAnarchyEquilibrium)
    healthy_anarchy_mycelial_service_covers_load

/-- Intrinsic chapel rate for this queue family: `3/4`. -/
def intrinsicQueueErgodicityRate (initialBound : Nat) :
    GeometricErgodicityRate :=
  { rateNumerator := 3
    rateDenominator := 4
    initialBound := initialBound + 1
    stepNumerator := 1
    stepDenominator := 2
    smallSetNumerator := 1
    smallSetDenominator := 2
    hStepPos := by decide
    hSmallSetPos := by decide
    hStepDenomPos := by decide
    hSmallSetDenomPos := by decide
    hInitialBoundPos := Nat.succ_pos initialBound
    hRatePos := by decide
    hRateDenomPos := by decide
    hRateLtOne := by decide }

/-- The intrinsic queue ergodicity rate is literally the `3/4` rate. -/
theorem intrinsic_queue_ergodicity_rate_is_three_four
    (initialBound : Nat) :
    (intrinsicQueueErgodicityRate initialBound).rateNumerator = 3 ∧
    (intrinsicQueueErgodicityRate initialBound).rateDenominator = 4 := by
  exact ⟨rfl, rfl⟩

/-- The intrinsic `3/4` queue rate is a strict contraction. -/
theorem intrinsic_queue_ergodicity_rate_contracts
    (initialBound : Nat) :
    (intrinsicQueueErgodicityRate initialBound).rateNumerator <
      (intrinsicQueueErgodicityRate initialBound).rateDenominator :=
  (intrinsicQueueErgodicityRate initialBound).hRateLtOne

/-- Use the current backlog as the positive initial bound carrier. -/
def queueErgodicityRateOfLoad (load : AnarchyQueueLoad) :
    GeometricErgodicityRate :=
  intrinsicQueueErgodicityRate (jacksonBacklog load)

/--
Every load in this finite queue family carries the same intrinsic `3/4`
ergodicity constraint; the initial bound changes, not the rate.
-/
theorem queue_load_ergodicity_rate_is_intrinsic_three_four
    (load : AnarchyQueueLoad) :
    (queueErgodicityRateOfLoad load).rateNumerator = 3 ∧
    (queueErgodicityRateOfLoad load).rateDenominator = 4 := by
  unfold queueErgodicityRateOfLoad
  exact intrinsic_queue_ergodicity_rate_is_three_four (jacksonBacklog load)

/-- The human Jackson reading of healthy anarchy inherits the intrinsic `3/4` rate. -/
theorem healthy_anarchy_human_queue_has_intrinsic_three_four_rate :
    (queueErgodicityRateOfLoad
        (queueLoadOfAnarchy distributedAnarchyEquilibrium)).rateNumerator = 3 ∧
    (queueErgodicityRateOfLoad
        (queueLoadOfAnarchy distributedAnarchyEquilibrium)).rateDenominator = 4 :=
  queue_load_ergodicity_rate_is_intrinsic_three_four
    (queueLoadOfAnarchy distributedAnarchyEquilibrium)

/--
Mycelium dominates the human capacity surface, but does not violate the
intrinsic chapel queue constraint: the bridge still records `3/4`.
-/
theorem mycelial_dominance_preserves_intrinsic_three_four_rate :
    humanJacksonServiceCapacity
        (serviceCapacity distributedAnarchyEquilibrium) <
      mycelialServiceCapacity
        (serviceCapacity distributedAnarchyEquilibrium) ∧
    (queueErgodicityRateOfLoad
        (queueLoadOfAnarchy distributedAnarchyEquilibrium)).rateNumerator = 3 ∧
    (queueErgodicityRateOfLoad
        (queueLoadOfAnarchy distributedAnarchyEquilibrium)).rateDenominator = 4 := by
  exact ⟨healthy_anarchy_mycelium_dominates_human_queue_service,
    healthy_anarchy_human_queue_has_intrinsic_three_four_rate.left,
    healthy_anarchy_human_queue_has_intrinsic_three_four_rate.right⟩

/--
The onward synthesis: for healthy anarchy, mycelial service weakly lowers the
same-load backlog, clears that backlog, and leaves the intrinsic `3/4`
ergodicity constraint unchanged.
-/
theorem healthy_anarchy_mycelial_backlog_and_rate_synthesis :
    mycelialBacklogForNodes
        (queueLoadOfAnarchy distributedAnarchyEquilibrium)
        (serviceCapacity distributedAnarchyEquilibrium) ≤
      humanBacklogForNodes
        (queueLoadOfAnarchy distributedAnarchyEquilibrium)
        (serviceCapacity distributedAnarchyEquilibrium) ∧
    mycelialBacklogForNodes
        (queueLoadOfAnarchy distributedAnarchyEquilibrium)
        (serviceCapacity distributedAnarchyEquilibrium) = 0 ∧
    (queueErgodicityRateOfLoad
        (queueLoadOfAnarchy distributedAnarchyEquilibrium)).rateNumerator = 3 ∧
    (queueErgodicityRateOfLoad
        (queueLoadOfAnarchy distributedAnarchyEquilibrium)).rateDenominator = 4 := by
  exact ⟨healthy_anarchy_mycelial_service_weakly_lowers_backlog,
    healthy_anarchy_mycelial_backlog_zero,
    healthy_anarchy_human_queue_has_intrinsic_three_four_rate.left,
    healthy_anarchy_human_queue_has_intrinsic_three_four_rate.right⟩

/-- Healthy anarchy clears the finite Jackson control queue. -/
theorem healthy_anarchy_jackson_control_stable :
    JacksonControlStable (queueLoadOfAnarchy distributedAnarchyEquilibrium) := by
  unfold JacksonControlStable
    queueLoadOfAnarchy
    totalArrival
    controlArrival
    serviceCapacity
    distributedAnarchyEquilibrium
    standingWaveControlPressure
    redundantAgreementPressure
    centralizationPressure
    distributedAntPhysarum
  native_decide

/-- Healthy anarchy has zero queue backlog in the bridge model. -/
theorem healthy_anarchy_jackson_backlog_zero :
    jacksonBacklog (queueLoadOfAnarchy distributedAnarchyEquilibrium) = 0 :=
  stable_control_queue_has_zero_backlog healthy_anarchy_jackson_control_stable

/-- Command-control leaves a positive queue backlog. -/
theorem command_control_jackson_backlog_positive :
    0 < jacksonBacklog (queueLoadOfAnarchy centralizedCommandEquilibrium) := by
  unfold jacksonBacklog
    queueLoadOfAnarchy
    totalArrival
    controlArrival
    serviceCapacity
    centralizedCommandEquilibrium
    standingWaveControlPressure
    redundantAgreementPressure
    centralizationPressure
    dictatorChokePoint
  native_decide

/--
Total anarchy saturation also leaves positive backlog: it preserves the same
control-pressure choke point while adding redundant agreement load.
-/
theorem total_anarchy_saturation_jackson_backlog_positive :
    0 < jacksonBacklog (queueLoadOfAnarchy totalAnarchyStandingWave) := by
  unfold jacksonBacklog
    queueLoadOfAnarchy
    totalArrival
    controlArrival
    serviceCapacity
    totalAnarchyStandingWave
    standingWaveControlPressure
    redundantAgreementPressure
    centralizationPressure
    dictatorChokePoint
  native_decide

/-- The concrete game tradeoff and the queue bridge agree for healthy anarchy. -/
theorem healthy_anarchy_tradeoff_clears_jackson_queue :
    picksCheapAndGoodNotFast
        (tradeoffPick distributedAnarchyEquilibrium centralizedCommandEquilibrium) ∧
      jacksonBacklog (queueLoadOfAnarchy distributedAnarchyEquilibrium) = 0 := by
  exact ⟨healthy_anarchy_tradeoff_pick_is_cheap_and_good,
    healthy_anarchy_jackson_backlog_zero⟩

/--
Command-control is the fast/control pick in the game, but that speed is bought
with positive Jackson backlog.
-/
theorem command_control_tradeoff_accumulates_jackson_backlog :
    picksOnlyFast
        (tradeoffPick centralizedCommandEquilibrium distributedAnarchyEquilibrium) ∧
      0 < jacksonBacklog (queueLoadOfAnarchy centralizedCommandEquilibrium) := by
  exact ⟨dictator_tradeoff_pick_is_only_fast_control,
    command_control_jackson_backlog_positive⟩

end AnarchyJacksonQueueBridge
end Gnosis
