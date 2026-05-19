import Gnosis.GodFormula
import Gnosis.IoGadflyTelemetryWitness
import Gnosis.IoKernelDaemonWitness
import Gnosis.SpectralNoiseEquilibrium

namespace Gnosis
namespace IoGarbageCollectorWitness

open SpectralNoiseEquilibrium

/-!
# Io Garbage Collector Witness

This module refines the Io gadfly-as-kernel-daemon reading into a garbage
collector witness.  The gadfly does not merely wake the pointer; it marks,
traces, moves, compacts, and finalizes Io's route ledger until the Egypt commit
closes the traversal.
-/

structure GarbageCollectorLifecycle where
  markPhase : Bool
  tracePhase : Bool
  moveObject : Bool
  compactPhase : Bool
  finalizePhase : Bool
  routeMarks : Nat
deriving Repr, DecidableEq

def ioGcLifecycle : GarbageCollectorLifecycle :=
  { markPhase := true
    tracePhase := true
    moveObject := true
    compactPhase := true
    finalizePhase := true
    routeMarks :=
      IoGadflyTelemetryWitness.routeNodeWrites
        IoGadflyTelemetryWitness.ioRouteLedger }

def gcLifecycleComplete (g : GarbageCollectorLifecycle) : Prop :=
  g.markPhase = true ∧
    g.tracePhase = true ∧
    g.moveObject = true ∧
    g.compactPhase = true ∧
    g.finalizePhase = true ∧
    0 < g.routeMarks

structure MovedObject where
  loweredPointer : Bool
  rescheduledByDaemon : Bool
  oldPastureStallAvoided : Bool
  finalLocationCommitted : Bool
deriving Repr, DecidableEq

def ioMovedObject : MovedObject :=
  { loweredPointer := true
    rescheduledByDaemon := true
    oldPastureStallAvoided := true
    finalLocationCommitted := true }

def movedObjectInvariant (o : MovedObject) : Prop :=
  o.loweredPointer = true ∧
    o.rescheduledByDaemon = true ∧
    o.oldPastureStallAvoided = true ∧
    o.finalLocationCommitted = true

structure GarbageCollectorHomology where
  watchdogDaemon : IoKernelDaemonWitness.KernelDaemon
  telemetryLedger : IoGadflyTelemetryWitness.RouteLedger
  commit : IoGadflyTelemetryWitness.MappingCommit
deriving Repr, DecidableEq

def ioGcHomology : GarbageCollectorHomology :=
  { watchdogDaemon := IoKernelDaemonWitness.ioGadflyDaemon
    telemetryLedger := IoGadflyTelemetryWitness.ioRouteLedger
    commit := IoGadflyTelemetryWitness.egyptCommit }

def gcReusesDaemonTelemetry (h : GarbageCollectorHomology) : Prop :=
  IoKernelDaemonWitness.kernelWatchdogDaemon h.watchdogDaemon ∧
    IoGadflyTelemetryWitness.routeCoverage h.telemetryLedger ∧
    IoGadflyTelemetryWitness.hardCompileCommit h.commit

def gcCost : BuleyUnit :=
  { waste := 3, opportunity := 4, diversity := 5 }

def gcFloorWeight : Nat :=
  godWeight gcCost.diversity gcCost.diversity

theorem io_gc_route_marks_are_five :
    ioGcLifecycle.routeMarks = 5 := by
  unfold ioGcLifecycle
  exact IoGadflyTelemetryWitness.io_route_writes_five_nodes

theorem io_gc_lifecycle_complete :
    gcLifecycleComplete ioGcLifecycle := by
  unfold gcLifecycleComplete ioGcLifecycle
  exact ⟨rfl, rfl, rfl, rfl, rfl, by
    rw [IoGadflyTelemetryWitness.io_route_writes_five_nodes]
    decide⟩

theorem io_is_moved_object :
    movedObjectInvariant ioMovedObject := by
  unfold movedObjectInvariant ioMovedObject
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem io_gc_reuses_daemon_and_telemetry :
    gcReusesDaemonTelemetry ioGcHomology := by
  unfold gcReusesDaemonTelemetry ioGcHomology
  exact ⟨IoKernelDaemonWitness.io_gadfly_is_kernel_daemon,
    IoGadflyTelemetryWitness.io_route_has_full_coverage,
    IoGadflyTelemetryWitness.egypt_is_hard_compile_commit⟩

theorem gc_cost_is_twelve :
    buleyUnitScore gcCost = 12 := by
  unfold gcCost buleyUnitScore
  decide

theorem gc_floor_weight_is_unit :
    gcFloorWeight = 1 := by
  unfold gcFloorWeight gcCost
  exact godWeight_floor 5

theorem io_garbage_collector_witness :
    gcLifecycleComplete ioGcLifecycle ∧
      movedObjectInvariant ioMovedObject ∧
      gcReusesDaemonTelemetry ioGcHomology ∧
      ioGcLifecycle.routeMarks = 5 ∧
      buleyUnitScore gcCost = 12 ∧
      gcFloorWeight = 1 := by
  exact ⟨io_gc_lifecycle_complete,
    io_is_moved_object,
    io_gc_reuses_daemon_and_telemetry,
    io_gc_route_marks_are_five,
    gc_cost_is_twelve,
    gc_floor_weight_is_unit⟩

end IoGarbageCollectorWitness
end Gnosis
