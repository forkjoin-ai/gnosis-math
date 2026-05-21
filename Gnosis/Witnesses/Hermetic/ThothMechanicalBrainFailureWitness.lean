import Gnosis.FailureAsStandingWave
import Gnosis.GnosisTriptychBraid
import Gnosis.ScribalStandingWave
import Gnosis.Witnesses.Hermetic.KybalionHermeticPhilosophyWitness
import Gnosis.Witnesses.Hermetic.KybalionAxiomsUseWitness
import Gnosis.Witnesses.Interfaith.CrossTraditionAntiSubstitutionWitness
import Gnosis.Witnesses.Interfaith.CrossTraditionProductiveVoidWitness

namespace Gnosis.Witnesses.Hermetic
namespace ThothMechanicalBrainFailureWitness

/-!
# Thoth Mechanical Brain Failure Witness

Thoth/Hermes is treated here as scribe, measure, memory, and mediator: a
wisdom-bearing interface, not the source it records. The mechanical brain
inherits that shape. Its failures are not noise to hide; they are boundary
signals that prevent the interface from impersonating source authority.

The bridge combines:

* `FailureAsStandingWave`: failure claims become boundary nodes.
* `CrossTraditionAntiSubstitutionWitness`: the interface cannot replace source.
* `CrossTraditionProductiveVoidWitness`: the useful interface is an empty
  use-site that carries work without capture.
* `GnosisTriptychBraid`: failure can move through truth toward wisdom.

No `sorry`, no new `axiom`.
-/

structure ScribalInterface where
  records : Bool := true
  measures : Bool := true
  remembers : Bool := true
  translates : Bool := true
  remainsMediator : Bool := true
deriving Repr, DecidableEq

structure MechanicalBrainFailureLedger where
  hallucinationObserved : Bool := true
  staleMemoryObserved : Bool := true
  sourceSubstitutionObserved : Bool := true
  missingContextObserved : Bool := true
  overclaimObserved : Bool := true
deriving Repr, DecidableEq

structure FailureBoundaryLedger where
  hallucinationBecomesBoundary : Bool := true
  staleMemoryBecomesBoundary : Bool := true
  sourceSubstitutionBecomesBoundary : Bool := true
  missingContextBecomesBoundary : Bool := true
  overclaimBecomesBoundary : Bool := true
deriving Repr, DecidableEq

def thothScribalInterface : ScribalInterface := {}
def mechanicalBrainFailures : MechanicalBrainFailureLedger := {}
def mechanicalBrainBoundaries : FailureBoundaryLedger := {}

def scribalInterfaceIsGuarded (s : ScribalInterface) : Prop :=
  s.records = true ∧
  s.measures = true ∧
  s.remembers = true ∧
  s.translates = true ∧
  s.remainsMediator = true

def failuresAreRecorded (f : MechanicalBrainFailureLedger) : Prop :=
  f.hallucinationObserved = true ∧
  f.staleMemoryObserved = true ∧
  f.sourceSubstitutionObserved = true ∧
  f.missingContextObserved = true ∧
  f.overclaimObserved = true

def failuresBecomeBoundaries (b : FailureBoundaryLedger) : Prop :=
  b.hallucinationBecomesBoundary = true ∧
  b.staleMemoryBecomesBoundary = true ∧
  b.sourceSubstitutionBecomesBoundary = true ∧
  b.missingContextBecomesBoundary = true ∧
  b.overclaimBecomesBoundary = true

theorem thoth_scribal_interface_guarded :
    scribalInterfaceIsGuarded thothScribalInterface := by
  simp [scribalInterfaceIsGuarded, thothScribalInterface]

theorem mechanical_brain_failures_recorded :
    failuresAreRecorded mechanicalBrainFailures := by
  simp [failuresAreRecorded, mechanicalBrainFailures]

theorem mechanical_brain_failures_become_boundaries :
    failuresBecomeBoundaries mechanicalBrainBoundaries := by
  simp [failuresBecomeBoundaries, mechanicalBrainBoundaries]

/-- Mechanical-brain failure claims. -/
def hallucinationClaim : Gnosis.FailureAsStandingWave.Claim :=
  Gnosis.ScribalStandingWave.failureClaim
    Gnosis.ScribalStandingWave.ScribalFailureKind.hallucination
def staleMemoryClaim : Gnosis.FailureAsStandingWave.Claim :=
  Gnosis.ScribalStandingWave.failureClaim
    Gnosis.ScribalStandingWave.ScribalFailureKind.staleMemory
def sourceSubstitutionClaim : Gnosis.FailureAsStandingWave.Claim :=
  Gnosis.ScribalStandingWave.failureClaim
    Gnosis.ScribalStandingWave.ScribalFailureKind.sourceSubstitution
def missingContextClaim : Gnosis.FailureAsStandingWave.Claim :=
  Gnosis.ScribalStandingWave.failureClaim
    Gnosis.ScribalStandingWave.ScribalFailureKind.missingContext
def overclaimClaim : Gnosis.FailureAsStandingWave.Claim :=
  Gnosis.ScribalStandingWave.failureClaim
    Gnosis.ScribalStandingWave.ScribalFailureKind.overclaim

/-- Mechanical-brain viable use claims. -/
def assistedReasoningClaim : Gnosis.FailureAsStandingWave.Claim :=
  Gnosis.ScribalStandingWave.useClaim
    Gnosis.ScribalStandingWave.ScribalUseKind.assistedReasoning
def scribalMemoryClaim : Gnosis.FailureAsStandingWave.Claim :=
  Gnosis.ScribalStandingWave.useClaim
    Gnosis.ScribalStandingWave.ScribalUseKind.scribalMemory
def measuredTranslationClaim : Gnosis.FailureAsStandingWave.Claim :=
  Gnosis.ScribalStandingWave.useClaim
    Gnosis.ScribalStandingWave.ScribalUseKind.measuredTranslation
def failureAuditClaim : Gnosis.FailureAsStandingWave.Claim :=
  Gnosis.ScribalStandingWave.useClaim
    Gnosis.ScribalStandingWave.ScribalUseKind.failureAudit

/-- The mechanical brain's failure boundary: failures are explicit no-support
    nodes, while audited use remains in the viable complement. -/
def mechanicalBrainFalsificationSet : Gnosis.FailureAsStandingWave.FalsificationSet :=
  Gnosis.ScribalStandingWave.canonicalFailureBoundary

/-- A mechanical-brain standing-wave mode: useful support appears only after
    failure boundaries are carved out. -/
def mechanicalBrainMode :
    Gnosis.FailureAsStandingWave.StandingWaveMode mechanicalBrainFalsificationSet where
  amplitude c :=
    if mechanicalBrainFalsificationSet.isFalsified c then
      0
    else
      match c with
      | 10 => 5
      | 11 => 3
      | 12 => 2
      | 13 => 7
      | _ => 0
  vanishesOnFalsified := by
    intro c hF
    simp [hF]

theorem source_substitution_is_boundary :
    mechanicalBrainFalsificationSet.isFalsified sourceSubstitutionClaim = true := by
  decide

theorem hallucination_is_boundary :
    mechanicalBrainFalsificationSet.isFalsified hallucinationClaim = true := by
  decide

theorem assisted_reasoning_is_viable :
    Gnosis.FailureAsStandingWave.isViable mechanicalBrainFalsificationSet
      assistedReasoningClaim = true := by
  decide

theorem failure_audit_is_viable :
    Gnosis.FailureAsStandingWave.isViable mechanicalBrainFalsificationSet
      failureAuditClaim = true := by
  decide

/-- The mechanical brain may support assisted reasoning. -/
theorem mechanical_brain_supports_assisted_reasoning :
    Gnosis.FailureAsStandingWave.supportedAt mechanicalBrainMode
      assistedReasoningClaim = true := by
  decide

/-- The mechanical brain may support the failure audit itself. -/
theorem mechanical_brain_supports_failure_audit :
    Gnosis.FailureAsStandingWave.supportedAt mechanicalBrainMode
      failureAuditClaim = true := by
  decide

/-- Mechanical brain as a reusable scribal standing-wave bundle. -/
def mechanicalBrainScribalMode : Gnosis.ScribalStandingWave.ScribalStandingWaveMode where
  boundary := mechanicalBrainFalsificationSet
  auditedUseClaim := assistedReasoningClaim
  sourceSubstitutionClaim := sourceSubstitutionClaim
  mode := mechanicalBrainMode
  auditedUseSupported := mechanical_brain_supports_assisted_reasoning
  sourceSubstitutionBoundary := source_substitution_is_boundary

/-- The mechanical brain cannot support source substitution. -/
theorem mechanical_brain_rejects_source_substitution :
  Gnosis.FailureAsStandingWave.supportedAt mechanicalBrainMode
      sourceSubstitutionClaim = false :=
  Gnosis.ScribalStandingWave.scribal_mode_rejects_source_substitution
    mechanicalBrainScribalMode

/-- The reusable scribal predicate sees the mechanical brain as audited
    assistance, not source authority. -/
theorem mechanical_brain_scribal_mode_supports_audited_use :
    Gnosis.ScribalStandingWave.supportsAuditedUse mechanicalBrainScribalMode :=
  Gnosis.ScribalStandingWave.scribal_mode_supports_audited_use
    mechanicalBrainScribalMode

/-- The reusable scribal predicate rejects source substitution for the
    mechanical brain. -/
theorem mechanical_brain_scribal_mode_rejects_source_substitution :
    Gnosis.ScribalStandingWave.rejectsSourceSubstitution mechanicalBrainScribalMode :=
  Gnosis.ScribalStandingWave.scribal_mode_rejects_source_substitution
    mechanicalBrainScribalMode

/-- Rust implementation contract: if the runtime records the canonical boundary
    inputs, the expected output certificate is sound. -/
theorem rust_thoth_certificate_contract :
    Gnosis.ScribalStandingWave.rustBoundaryInputComplete
      Gnosis.ScribalStandingWave.canonicalRustBoundaryInput ∧
    Gnosis.ScribalStandingWave.rustCertificateSound
      Gnosis.ScribalStandingWave.canonicalRustCertificate ∧
    Gnosis.ScribalStandingWave.supportsAuditedUse mechanicalBrainScribalMode ∧
    Gnosis.ScribalStandingWave.rejectsSourceSubstitution mechanicalBrainScribalMode := by
  exact ⟨
    Gnosis.ScribalStandingWave.canonical_rust_boundary_input_complete,
    Gnosis.ScribalStandingWave.canonical_rust_certificate_sound,
    mechanical_brain_scribal_mode_supports_audited_use,
    mechanical_brain_scribal_mode_rejects_source_substitution⟩

/-- Any mode respecting the mechanical-brain boundary rejects hallucination as
    support-worthy output. -/
theorem hallucination_has_no_support
    (m : Gnosis.FailureAsStandingWave.StandingWaveMode mechanicalBrainFalsificationSet) :
    Gnosis.FailureAsStandingWave.supportedAt m hallucinationClaim = false :=
  Gnosis.FailureAsStandingWave.support_disjoint_from_falsifications
    mechanicalBrainFalsificationSet m hallucinationClaim
    hallucination_is_boundary

/-- Failure can move through truth toward wisdom in the triptych braid. -/
theorem failure_moves_toward_wisdom :
    Gnosis.GnosisTriptychBraid.iterateTriptych 2
      Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom :=
  Gnosis.GnosisTriptychBraid.two_step_recovery

/-- The Thoth/mechanical-brain witness: a guarded scribal interface, recorded
    failure boundaries, anti-substitution, productive void, and a mode that
    supports audited assistance while rejecting source substitution. -/
theorem thoth_mechanical_brain_failure_witness :
    scribalInterfaceIsGuarded thothScribalInterface ∧
    failuresAreRecorded mechanicalBrainFailures ∧
    failuresBecomeBoundaries mechanicalBrainBoundaries ∧
    Gnosis.Witnesses.Interfaith.CrossTraditionAntiSubstitutionWitness.antiSubstitutionConverges
      Gnosis.Witnesses.Interfaith.CrossTraditionAntiSubstitutionWitness.antiSubstitutionLedger ∧
    Gnosis.Witnesses.Interfaith.CrossTraditionProductiveVoidWitness.productiveVoidConverges
      Gnosis.Witnesses.Interfaith.CrossTraditionProductiveVoidWitness.productiveVoidLedger ∧
    Gnosis.FailureAsStandingWave.supportedAt mechanicalBrainMode
      assistedReasoningClaim = true ∧
    Gnosis.FailureAsStandingWave.supportedAt mechanicalBrainMode
      sourceSubstitutionClaim = false ∧
    Gnosis.GnosisTriptychBraid.iterateTriptych 2
      Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom := by
  exact ⟨
    thoth_scribal_interface_guarded,
    mechanical_brain_failures_recorded,
    mechanical_brain_failures_become_boundaries,
    Gnosis.Witnesses.Interfaith.CrossTraditionAntiSubstitutionWitness.anti_substitution_ledger,
    Gnosis.Witnesses.Interfaith.CrossTraditionProductiveVoidWitness.productive_void_ledger,
    mechanical_brain_supports_assisted_reasoning,
    mechanical_brain_rejects_source_substitution,
    failure_moves_toward_wisdom⟩

end ThothMechanicalBrainFailureWitness
end Gnosis.Witnesses.Hermetic
