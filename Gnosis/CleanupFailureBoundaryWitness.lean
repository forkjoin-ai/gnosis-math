import Gnosis.CompleteCleanupSystemClosureWitness
import Gnosis.GodFormula
import Gnosis.SpectralNoiseEquilibrium

namespace Gnosis
namespace CleanupFailureBoundaryWitness

open SpectralNoiseEquilibrium

/-!
# Cleanup Failure Boundary Witness

This module closes the cleanup-system line from the negative side.  The
positive closure proves the stack works; this finite boundary names the exact
ways that closure fails.
-/

inductive CleanupFailureMode where
  | missedTelemetryMark
  | daemonStarvation
  | failedCompaction
  | apoptosisBelowThreshold
  | autophagyNonMerge
  | proteasomeBacklog
deriving Repr, DecidableEq

def cleanupFailureModes : List CleanupFailureMode :=
  [ .missedTelemetryMark
  , .daemonStarvation
  , .failedCompaction
  , .apoptosisBelowThreshold
  , .autophagyNonMerge
  , .proteasomeBacklog
  ]

def failedCleanupSystem (mode : CleanupFailureMode) :
    CompleteCleanupSystemClosureWitness.CompleteCleanupSystem :=
  let closed := CompleteCleanupSystemClosureWitness.completeCleanupSystem
  match mode with
  | .missedTelemetryMark =>
      { closed with telemetryCoverage := false, routeMarks := 4 }
  | .daemonStarvation =>
      { closed with daemonWatchdog := false }
  | .failedCompaction =>
      { closed with gcLifecycle := false }
  | .apoptosisBelowThreshold =>
      { closed with runtimeAtlas := false, cleanupMechanisms := 4 }
  | .autophagyNonMerge =>
      { closed with autophagyBridge := false, recyclingStages := 3 }
  | .proteasomeBacklog =>
      { closed with proteostasisBridge := false, proteostasisStages := 4 }

def closureBroken
    (system : CompleteCleanupSystemClosureWitness.CompleteCleanupSystem) : Prop :=
  ¬ CompleteCleanupSystemClosureWitness.completeCleanupSystemClosed system

def boundaryCost : BuleyUnit :=
  { waste := 6, opportunity := 3, diversity := 3 }

def boundaryFloorWeight : Nat :=
  godWeight boundaryCost.diversity boundaryCost.diversity

theorem failure_mode_count_is_six :
    cleanupFailureModes.length = 6 := by
  unfold cleanupFailureModes
  decide

theorem missed_telemetry_mark_breaks_closure :
    closureBroken (failedCleanupSystem .missedTelemetryMark) := by
  unfold closureBroken CompleteCleanupSystemClosureWitness.completeCleanupSystemClosed
    failedCleanupSystem CompleteCleanupSystemClosureWitness.completeCleanupSystem
  intro h
  exact Bool.false_ne_true h.1

theorem daemon_starvation_breaks_closure :
    closureBroken (failedCleanupSystem .daemonStarvation) := by
  unfold closureBroken CompleteCleanupSystemClosureWitness.completeCleanupSystemClosed
    failedCleanupSystem CompleteCleanupSystemClosureWitness.completeCleanupSystem
  intro h
  exact Bool.false_ne_true h.2.1

theorem failed_compaction_breaks_closure :
    closureBroken (failedCleanupSystem .failedCompaction) := by
  unfold closureBroken CompleteCleanupSystemClosureWitness.completeCleanupSystemClosed
    failedCleanupSystem CompleteCleanupSystemClosureWitness.completeCleanupSystem
  intro h
  exact Bool.false_ne_true h.2.2.1

theorem apoptosis_below_threshold_breaks_closure :
    closureBroken (failedCleanupSystem .apoptosisBelowThreshold) := by
  unfold closureBroken CompleteCleanupSystemClosureWitness.completeCleanupSystemClosed
    failedCleanupSystem CompleteCleanupSystemClosureWitness.completeCleanupSystem
  intro h
  exact Bool.false_ne_true h.2.2.2.1

theorem autophagy_non_merge_breaks_closure :
    closureBroken (failedCleanupSystem .autophagyNonMerge) := by
  unfold closureBroken CompleteCleanupSystemClosureWitness.completeCleanupSystemClosed
    failedCleanupSystem CompleteCleanupSystemClosureWitness.completeCleanupSystem
  intro h
  exact Bool.false_ne_true h.2.2.2.2.1

theorem proteasome_backlog_breaks_closure :
    closureBroken (failedCleanupSystem .proteasomeBacklog) := by
  unfold closureBroken CompleteCleanupSystemClosureWitness.completeCleanupSystemClosed
    failedCleanupSystem CompleteCleanupSystemClosureWitness.completeCleanupSystem
  intro h
  exact Bool.false_ne_true h.2.2.2.2.2.1

theorem boundary_cost_is_twelve :
    buleyUnitScore boundaryCost = 12 := by
  unfold boundaryCost buleyUnitScore
  decide

theorem boundary_floor_weight_is_unit :
    boundaryFloorWeight = 1 := by
  unfold boundaryFloorWeight boundaryCost
  exact godWeight_floor 3

theorem cleanup_failure_boundary_witness :
    cleanupFailureModes.length = 6 ∧
      closureBroken (failedCleanupSystem .missedTelemetryMark) ∧
      closureBroken (failedCleanupSystem .daemonStarvation) ∧
      closureBroken (failedCleanupSystem .failedCompaction) ∧
      closureBroken (failedCleanupSystem .apoptosisBelowThreshold) ∧
      closureBroken (failedCleanupSystem .autophagyNonMerge) ∧
      closureBroken (failedCleanupSystem .proteasomeBacklog) ∧
      buleyUnitScore boundaryCost = 12 ∧
      boundaryFloorWeight = 1 := by
  exact ⟨failure_mode_count_is_six,
    missed_telemetry_mark_breaks_closure,
    daemon_starvation_breaks_closure,
    failed_compaction_breaks_closure,
    apoptosis_below_threshold_breaks_closure,
    autophagy_non_merge_breaks_closure,
    proteasome_backlog_breaks_closure,
    boundary_cost_is_twelve,
    boundary_floor_weight_is_unit⟩

end CleanupFailureBoundaryWitness
end Gnosis
