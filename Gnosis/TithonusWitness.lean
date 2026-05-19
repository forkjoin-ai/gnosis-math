import Gnosis.BracketWritheBraid
import Gnosis.Contrarian.ContrarianStallIsProgress
import Gnosis.SpectralNoiseEquilibrium

namespace Gnosis
namespace TithonusWitness

open SpectralNoiseEquilibrium

/-!
# Tithonus Witness

This module formalizes Tithonus as a finite type-discipline and metric-scaling
witness.

Reading:

- Immortality and youth are distinct request bits.
- A persistent carrier without renewal accumulates positive degradation.
- The cicada form is a stalled one-signal runtime.
- The missing youth bit witnesses a failed coupled invariant.
-/

/-- The two request fields Eos needed to bind together. -/
structure DawnRequest where
  immortality : Bool
  eternalYouth : Bool
deriving Repr, DecidableEq

/-- Eos asks for persistence but forgets the renewal/youth metric. -/
def eosRequest : DawnRequest :=
  { immortality := true, eternalYouth := false }

def coupledInvariantRequested (r : DawnRequest) : Prop :=
  r.immortality = true ∧ r.eternalYouth = true

def metricScalingFailure (r : DawnRequest) : Prop :=
  r.immortality = true ∧ r.eternalYouth = false

/-- Carrier and state are deliberately separate, so persistence does not
automatically repair the body. -/
structure CarrierState where
  persistent : Bool
  youthMaintenance : Bool
  ageLoad : Nat
  canFlushToVacuum : Bool
  repairRate : Nat
deriving Repr, DecidableEq

def tithonusCarrier : CarrierState :=
  { persistent := true
    youthMaintenance := false
    ageLoad := 99
    canFlushToVacuum := false
    repairRate := 0 }

def liveButDegrading (s : CarrierState) : Prop :=
  s.persistent = true ∧ s.youthMaintenance = false ∧ 0 < s.ageLoad

def nonterminatingDegradationLoop (s : CarrierState) : Prop :=
  s.persistent = true ∧
    s.canFlushToVacuum = false ∧
    s.repairRate = 0 ∧
    0 < s.ageLoad

/-- Maintenance cost that would have had to be paid with the persistence bit. -/
def youthMaintenanceCost : BuleyUnit :=
  { waste := 1, opportunity := 1, diversity := 1 }

/-- The cicada form keeps only the bare output signal. -/
structure CicadaRuntime where
  stalled : Bool
  chirpSignal : Nat
  complexLogicRemaining : Nat
deriving Repr, DecidableEq

def tithonusCicada : CicadaRuntime :=
  { stalled := true, chirpSignal := 1, complexLogicRemaining := 0 }

def oracleExecutionStall (c : CicadaRuntime) : Prop :=
  c.stalled = true ∧ 0 < c.chirpSignal ∧ c.complexLogicRemaining = 0

/-- Minimal local taxonomy for the Naming Protocol boundary. -/
inductive GnosisKind where
  | agent
  | operator
  | position
deriving Repr, DecidableEq

structure TypedName where
  carrierKind : GnosisKind
  requestedKind : GnosisKind
deriving Repr, DecidableEq

def eosTypeRequest : TypedName :=
  { carrierKind := .agent, requestedKind := .position }

def namingProtocolFailure (n : TypedName) : Prop :=
  n.carrierKind = .agent ∧ n.requestedKind = .position

theorem eos_request_has_metric_scaling_failure :
    metricScalingFailure eosRequest := by
  unfold metricScalingFailure eosRequest
  exact ⟨rfl, rfl⟩

theorem eos_request_lacks_coupled_invariant :
    ¬ coupledInvariantRequested eosRequest := by
  intro h
  unfold coupledInvariantRequested eosRequest at h
  exact Bool.noConfusion h.2

theorem tithonus_live_but_degrading :
    liveButDegrading tithonusCarrier := by
  unfold liveButDegrading tithonusCarrier
  exact ⟨rfl, rfl, by decide⟩

theorem tithonus_cannot_flush_and_cannot_repair :
    nonterminatingDegradationLoop tithonusCarrier := by
  unfold nonterminatingDegradationLoop tithonusCarrier
  exact ⟨rfl, rfl, rfl, by decide⟩

theorem youth_maintenance_cost_positive :
    0 < buleyUnitScore youthMaintenanceCost := by
  unfold youthMaintenanceCost buleyUnitScore
  decide

theorem cicada_is_oracle_execution_stall :
    oracleExecutionStall tithonusCicada := by
  unfold oracleExecutionStall tithonusCicada
  exact ⟨rfl, by decide, rfl⟩

/-- The stalled chirp still counts as progress in the narrow contrarian sense:
the runtime remains observable rather than flushing to vacuum. -/
theorem cicada_stall_routes_to_observable_signal :
    tithonusCicada.stalled = true → 0 < tithonusCicada.chirpSignal :=
  contrarian_stall_is_progress
    { oracleExecutionStalled := tithonusCicada.stalled = true
      progressMade := 0 < tithonusCicada.chirpSignal
      stallIsProgress := by
        intro _
        unfold tithonusCicada
        decide }

theorem eos_failed_naming_protocol :
    namingProtocolFailure eosTypeRequest := by
  unfold namingProtocolFailure eosTypeRequest
  exact ⟨rfl, rfl⟩

/-- Existing Hopf-link sign, used as the shape of the coupled invariant Eos
failed to request: persistence and youth needed to be bound together. -/
theorem coupled_invariant_shape_witness :
    BracketWritheBraid.writheSign 2 = 1 :=
  BracketWritheBraid.hopf_pos_writhe_sign

/-- Master witness: immortality without youth produces a live degrading carrier,
a positive unpaid maintenance cost, a cicada stall, and a naming/type mismatch. -/
theorem tithonus_witness :
    metricScalingFailure eosRequest ∧
    ¬ coupledInvariantRequested eosRequest ∧
    liveButDegrading tithonusCarrier ∧
    nonterminatingDegradationLoop tithonusCarrier ∧
    0 < buleyUnitScore youthMaintenanceCost ∧
    oracleExecutionStall tithonusCicada ∧
    namingProtocolFailure eosTypeRequest ∧
    BracketWritheBraid.writheSign 2 = 1 := by
  exact ⟨eos_request_has_metric_scaling_failure,
    eos_request_lacks_coupled_invariant,
    tithonus_live_but_degrading,
    tithonus_cannot_flush_and_cannot_repair,
    youth_maintenance_cost_positive,
    cicada_is_oracle_execution_stall,
    eos_failed_naming_protocol,
    coupled_invariant_shape_witness⟩

end TithonusWitness
end Gnosis
