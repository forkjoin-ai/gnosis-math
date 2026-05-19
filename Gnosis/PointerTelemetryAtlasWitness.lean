import Gnosis.GodFormula
import Gnosis.IoGadflyTelemetryWitness
import Gnosis.SpectralNoiseEquilibrium

namespace Gnosis
namespace PointerTelemetryAtlasWitness

open SpectralNoiseEquilibrium
open IoGadflyTelemetryWitness

/-!
# Pointer Telemetry Atlas Witness

Generalizes the Io gadfly pattern into a reusable finite atlas: a lowered
pointer, an interrupt signal, route-ledger writes, anti-stall motion, and a
final commit.
-/

inductive PointerCase where
  | io
  | leto
  | odysseus
deriving Repr, DecidableEq

structure TelemetryPattern where
  pointer : PointerCase
  loweredPointer : Bool
  interruptSignal : Bool
  routeLedgerWrites : Nat
  antiStallMotion : Bool
  finalCommit : Bool
deriving Repr, DecidableEq

def ioPattern : TelemetryPattern :=
  { pointer := .io
    loweredPointer := true
    interruptSignal := true
    routeLedgerWrites := IoGadflyTelemetryWitness.routeNodeWrites
      IoGadflyTelemetryWitness.ioRouteLedger
    antiStallMotion := true
    finalCommit := true }

def letoPattern : TelemetryPattern :=
  { pointer := .leto
    loweredPointer := false
    interruptSignal := true
    routeLedgerWrites := 4
    antiStallMotion := true
    finalCommit := true }

def odysseusPattern : TelemetryPattern :=
  { pointer := .odysseus
    loweredPointer := false
    interruptSignal := true
    routeLedgerWrites := 10
    antiStallMotion := true
    finalCommit := true }

def telemetryAtlasEntry (p : TelemetryPattern) : Prop :=
  p.interruptSignal = true ∧ 0 < p.routeLedgerWrites ∧
    p.antiStallMotion = true ∧ p.finalCommit = true

def loweredTelemetryEntry (p : TelemetryPattern) : Prop :=
  telemetryAtlasEntry p ∧ p.loweredPointer = true

def atlasCoverage : Nat :=
  ioPattern.routeLedgerWrites + letoPattern.routeLedgerWrites +
    odysseusPattern.routeLedgerWrites

def pointerTelemetryCost : BuleyUnit :=
  { waste := 3, opportunity := 4, diversity := 5 }

def pointerAtlasFloorWeight : Nat :=
  godWeight pointerTelemetryCost.diversity pointerTelemetryCost.diversity

theorem io_pattern_reuses_gadfly_route_writes :
    ioPattern.routeLedgerWrites = 5 := by
  unfold ioPattern
  exact IoGadflyTelemetryWitness.io_route_writes_five_nodes

theorem io_is_lowered_telemetry_entry :
    loweredTelemetryEntry ioPattern := by
  unfold loweredTelemetryEntry telemetryAtlasEntry ioPattern
  exact ⟨⟨rfl, by decide, rfl, rfl⟩, rfl⟩

theorem leto_is_telemetry_entry :
    telemetryAtlasEntry letoPattern := by
  unfold telemetryAtlasEntry letoPattern
  exact ⟨rfl, by decide, rfl, rfl⟩

theorem odysseus_is_telemetry_entry :
    telemetryAtlasEntry odysseusPattern := by
  unfold telemetryAtlasEntry odysseusPattern
  exact ⟨rfl, by decide, rfl, rfl⟩

theorem atlas_coverage_is_nineteen :
    atlasCoverage = 19 := by
  unfold atlasCoverage ioPattern letoPattern odysseusPattern
  decide

theorem pointer_telemetry_cost_is_twelve :
    buleyUnitScore pointerTelemetryCost = 12 := by
  unfold pointerTelemetryCost buleyUnitScore
  decide

theorem pointer_atlas_floor_weight_is_unit :
    pointerAtlasFloorWeight = 1 := by
  unfold pointerAtlasFloorWeight pointerTelemetryCost
  exact godWeight_floor 5

theorem pointer_telemetry_atlas_witness :
    loweredTelemetryEntry ioPattern ∧
    telemetryAtlasEntry letoPattern ∧
    telemetryAtlasEntry odysseusPattern ∧
    atlasCoverage = 19 ∧
    buleyUnitScore pointerTelemetryCost = 12 ∧
    pointerAtlasFloorWeight = 1 := by
  exact ⟨io_is_lowered_telemetry_entry,
    leto_is_telemetry_entry,
    odysseus_is_telemetry_entry,
    atlas_coverage_is_nineteen,
    pointer_telemetry_cost_is_twelve,
    pointer_atlas_floor_weight_is_unit⟩

end PointerTelemetryAtlasWitness
end Gnosis
