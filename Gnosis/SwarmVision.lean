import Init
import Gnosis.RemoteCacheKeyTeleportation

namespace Gnosis
namespace SwarmVision

open RemoteCacheKeyTeleportation

/-!
# SwarmVision

Rich sensory telemetry for the ASCII swarm.  The floating-point fields mirror
runtime sensor readings, while the Nat milli-unit mirrors give the Init-level
proof surface a deterministic gate for thermal, optical, and power readiness.
-/

/-- Rich sensory telemetry for a single node. -/
structure SensorTelemetry where
  nodeId : Nat
  temperatureCelsius : Float
  temperatureMilliCelsius : Nat
  lightIntensityLumen : Float
  lightMilliLumen : Nat
  powerDrawMilliamp : Float
  powerDrawMicroamp : Nat
  voltageReference : Float
  voltageMillivolt : Nat
  isThermalThrottled : Bool
  lastHeartbeat : Nat

/-- A node is thermally safe exactly when it is below the configured thermal
limit and not already throttling. -/
def sensorThermallyStable (limitMilliCelsius : Nat) (node : SensorTelemetry) : Bool :=
  decide (node.temperatureMilliCelsius < limitMilliCelsius) && !node.isThermalThrottled

/-- A node has enough optical signal for ASCII/crystal projection calibration. -/
def sensorOpticallyVisible (minimumMilliLumen : Nat) (node : SensorTelemetry) : Bool :=
  decide (minimumMilliLumen ≤ node.lightMilliLumen)

/-- A node is inside the allowed current budget. -/
def sensorPowerStable (maximumMicroamp : Nat) (node : SensorTelemetry) : Bool :=
  decide (node.powerDrawMicroamp ≤ maximumMicroamp)

/-- Node-level physical readiness: thermal, optical, and power gates all pass. -/
def sensorReady
    (thermalLimitMilliCelsius minimumMilliLumen maximumMicroamp : Nat)
    (node : SensorTelemetry) : Bool :=
  sensorThermallyStable thermalLimitMilliCelsius node &&
  sensorOpticallyVisible minimumMilliLumen node &&
  sensorPowerStable maximumMicroamp node

/-- The total enriched state of the 12-node ASCII swarm. -/
structure SwarmState where
  nodes : List SensorTelemetry
  expectedNodeCount : Nat := 12
  thermalLimitCelsius : Float := 65.0
  thermalLimitMilliCelsius : Nat := 65000
  minimumLightLumen : Float := 1.0
  minimumLightMilliLumen : Nat := 1000
  maximumPowerMilliamp : Float := 500.0
  maximumPowerMicroamp : Nat := 500000
  isStable : Bool :=
    nodes.all (sensorReady
      thermalLimitMilliCelsius
      minimumLightMilliLumen
      maximumPowerMicroamp)

/-- Formal integrity of the swarm as an ER-bridge component. -/
structure SwarmIntegrityWitness where
  swarm : SwarmState
  isSpatiallyAligned : Bool
  consistentWithBoundaryTrace : Bool
  replay : RemoteReplayWitness := earthMarsReplayWitness

/-- Predicate defining when the swarm is holographically ready for a
computation hop. -/
def isHolographicallyReady (w : SwarmIntegrityWitness) : Bool :=
  w.swarm.isStable &&
  w.isSpatiallyAligned &&
  w.consistentWithBoundaryTrace

theorem ready_bool_left {a b c : Bool} (h : (a && b && c) = true) :
    a = true := by
  cases a <;> cases b <;> cases c <;> first | rfl | cases h

theorem ready_bool_middle {a b c : Bool} (h : (a && b && c) = true) :
    b = true := by
  cases a <;> cases b <;> cases c <;> first | rfl | cases h

theorem ready_bool_right {a b c : Bool} (h : (a && b && c) = true) :
    c = true := by
  cases a <;> cases b <;> cases c <;> first | rfl | cases h

/-- Safe replay execution packages the physical readiness gate together with
the logical remote replay theorem surface. -/
structure SafeReplayExecution where
  integrity : SwarmIntegrityWitness
  ready : isHolographicallyReady integrity = true
  cachedReplay :
    AmplituhedronCoordinatorContract.decodeEntryFromDecision
      (AmplituhedronCoordinatorContract.coordinatorDecision
        (hitVerdicts integrity.replay.tailResidualLen integrity.replay.stationCount)) =
      AmplituhedronCoordinatorContract.DecodeEntry.viaCachedReplay
  zeroGeodesic :
    EREPR.geodesicLength integrity.replay.sourceDimension
      integrity.replay.targetDimension = 0

/-- The hardware gate is intentionally fail-closed: only a fully ready integrity
witness can be promoted to safe replay execution. -/
def safe_computation_hop (w : SwarmIntegrityWitness)
    (hReady : isHolographicallyReady w = true) :
    SafeReplayExecution := by
  refine
    { integrity := w
      ready := hReady
      cachedReplay := ?_
      zeroGeodesic := ?_ }
  · exact all_hit_key_packet_selects_cached_replay
      w.replay.tailResidualLen w.replay.stationCount
  · exact EREPR.geodesic_zero_on_trace_match
      w.replay.sourceDimension w.replay.targetDimension
      w.replay.sourceTargetEntangled

/-- A ready swarm is stable at the top-level physical gate. -/
theorem holographic_ready_implies_swarm_stable
    (w : SwarmIntegrityWitness)
    (hReady : isHolographicallyReady w = true) :
    w.swarm.isStable = true := by
  unfold isHolographicallyReady at hReady
  exact ready_bool_left hReady

/-- A ready swarm is spatially aligned. -/
theorem holographic_ready_implies_spatial_alignment
    (w : SwarmIntegrityWitness)
    (hReady : isHolographicallyReady w = true) :
    w.isSpatiallyAligned = true := by
  unfold isHolographicallyReady at hReady
  exact ready_bool_middle hReady

/-- A ready swarm has a boundary-trace consistency witness. -/
theorem holographic_ready_implies_boundary_consistency
    (w : SwarmIntegrityWitness)
    (hReady : isHolographicallyReady w = true) :
    w.consistentWithBoundaryTrace = true := by
  unfold isHolographicallyReady at hReady
  exact ready_bool_right hReady

end SwarmVision
end Gnosis
