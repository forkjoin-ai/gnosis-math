import Gnosis.GodFormula
import Gnosis.SpectralNoiseEquilibrium

namespace Gnosis
namespace IoGadflyTelemetryWitness

open SpectralNoiseEquilibrium

/-!
# Io / Gadfly Telemetry Witness

Finite witness for Io as a floating pointer driven by active telemetry.  The
gadfly is modeled as a periodic interrupt that prevents pasture-stall, forces
position recomputation, writes route nodes into the ledger, and commits the
mapping kernel when Io reaches Egypt.
-/

inductive RouteNode where
  | heraTemple
  | argusWatch
  | bosphorus
  | ionianSea
  | egypt
deriving Repr, DecidableEq

structure FloatingPointer where
  sourceNamespace : RouteNode
  currentTypeLowered : Bool
  detachedFromSource : Bool
  widerManifoldActive : Bool
deriving Repr, DecidableEq

def ioPointer : FloatingPointer :=
  { sourceNamespace := .heraTemple
    currentTypeLowered := true
    detachedFromSource := true
    widerManifoldActive := true }

def floatingPointer (p : FloatingPointer) : Prop :=
  p.sourceNamespace = .heraTemple ∧ p.currentTypeLowered = true ∧
    p.detachedFromSource = true ∧ p.widerManifoldActive = true

structure GadflyInterrupt where
  periodicSting : Bool
  highFrequency : Bool
  preventsStall : Bool
  recomputesPosition : Bool
deriving Repr, DecidableEq

def heraGadfly : GadflyInterrupt :=
  { periodicSting := true
    highFrequency := true
    preventsStall := true
    recomputesPosition := true }

def activeTelemetry (g : GadflyInterrupt) : Prop :=
  g.periodicSting = true ∧ g.highFrequency = true ∧
    g.preventsStall = true ∧ g.recomputesPosition = true

structure RouteLedger where
  visitedTemple : Bool
  visitedArgusWatch : Bool
  visitedBosphorus : Bool
  visitedIonianSea : Bool
  visitedEgypt : Bool
deriving Repr, DecidableEq

def ioRouteLedger : RouteLedger :=
  { visitedTemple := true
    visitedArgusWatch := true
    visitedBosphorus := true
    visitedIonianSea := true
    visitedEgypt := true }

def routeCoverage (r : RouteLedger) : Prop :=
  r.visitedTemple = true ∧ r.visitedArgusWatch = true ∧
    r.visitedBosphorus = true ∧ r.visitedIonianSea = true ∧
    r.visitedEgypt = true

def routeNodeWrites (r : RouteLedger) : Nat :=
  (if r.visitedTemple then 1 else 0) +
    (if r.visitedArgusWatch then 1 else 0) +
    (if r.visitedBosphorus then 1 else 0) +
    (if r.visitedIonianSea then 1 else 0) +
    (if r.visitedEgypt then 1 else 0)

structure MappingCommit where
  reachedEgypt : Bool
  restoredHumanForm : Bool
  mappingKernelComplete : Bool
deriving Repr, DecidableEq

def egyptCommit : MappingCommit :=
  { reachedEgypt := true
    restoredHumanForm := true
    mappingKernelComplete := true }

def hardCompileCommit (c : MappingCommit) : Prop :=
  c.reachedEgypt = true ∧ c.restoredHumanForm = true ∧
    c.mappingKernelComplete = true

def telemetryCost : BuleyUnit :=
  { waste := 2, opportunity := 4, diversity := 6 }

def fullCoverageFloorWeight : Nat :=
  godWeight telemetryCost.diversity telemetryCost.diversity

theorem io_is_floating_pointer :
    floatingPointer ioPointer := by
  unfold floatingPointer ioPointer
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem gadfly_is_active_telemetry :
    activeTelemetry heraGadfly := by
  unfold activeTelemetry heraGadfly
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem io_route_has_full_coverage :
    routeCoverage ioRouteLedger := by
  unfold routeCoverage ioRouteLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem io_route_writes_five_nodes :
    routeNodeWrites ioRouteLedger = 5 := by
  unfold routeNodeWrites ioRouteLedger
  decide

theorem egypt_is_hard_compile_commit :
    hardCompileCommit egyptCommit := by
  unfold hardCompileCommit egyptCommit
  exact ⟨rfl, rfl, rfl⟩

theorem telemetry_cost_is_twelve :
    buleyUnitScore telemetryCost = 12 := by
  unfold telemetryCost buleyUnitScore
  decide

theorem full_coverage_floor_weight_is_unit :
    fullCoverageFloorWeight = 1 := by
  unfold fullCoverageFloorWeight telemetryCost
  exact godWeight_floor 6

theorem io_gadfly_telemetry_witness :
    floatingPointer ioPointer ∧
    activeTelemetry heraGadfly ∧
    routeCoverage ioRouteLedger ∧
    routeNodeWrites ioRouteLedger = 5 ∧
    hardCompileCommit egyptCommit ∧
    buleyUnitScore telemetryCost = 12 ∧
    fullCoverageFloorWeight = 1 := by
  exact ⟨io_is_floating_pointer,
    gadfly_is_active_telemetry,
    io_route_has_full_coverage,
    io_route_writes_five_nodes,
    egypt_is_hard_compile_commit,
    telemetry_cost_is_twelve,
    full_coverage_floor_weight_is_unit⟩

end IoGadflyTelemetryWitness
end Gnosis
