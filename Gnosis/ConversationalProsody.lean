import Gnosis.ConversationalDodgeball
import Gnosis.SpeakerStandingWaveDiarization
import Gnosis.ScribalStandingWave

namespace Gnosis
namespace ConversationalProsody

open Gnosis.ConversationalDodgeball
open SpeakerStandingWaveDiarization

/-!
# Conversational Prosody

Finite vacuum-pressure stream gate for question/answer closure.

Sentence prosody asks whether a sentence has enough cadence to close.
Conversational prosody lifts that shape to dialogue: an open question creates a
vacuum stream. Answer content, boundary declaration, cadence, and acceptance
criteria provide drainage/conductance. If the stream is not drained below the
finite threshold, Thoth should not pretend closure; it should route the residue
to glossolalia-style semiotic exploration or to an audit gap.
-/

/-- Finite runtime dials extracted from a conversation turn. -/
structure ConversationalProsodySignal where
  questionVacuum : Nat
  answerDrain : Nat
  boundaryDrain : Nat
  silenceResidue : Nat
  ambiguityResidue : Nat
  reserveResidue : Nat
  cadenceConductance : Nat
  acceptanceCriteriaDrain : Nat
  deriving DecidableEq, Repr

/-- Reynolds-like gate: drainage must dominate the vacuum stream by a finite
    multiple, remaining vacuum must stay bounded, and cadence conductance must
    be stable enough to fold. -/
structure ConversationalReynoldsGate where
  reynoldsThreshold : Nat
  residualThreshold : Nat
  cadenceThreshold : Nat
  deriving DecidableEq, Repr

/-- Runtime stream projection: source vacuum, finite conductance, and remaining
    residue. This is the new conversational primitive: the open slot streams
    pressure until enough conductance drains it. -/
structure VacuumPressureStream where
  sourceVacuum : Nat
  conductance : Nat
  residue : Nat
  deriving DecidableEq, Repr

/-- Pressure keeping the question open. The `+1` appears at the ratio site below
    to avoid division-by-zero rather than hiding pressure here. -/
def vacuumStream (signal : ConversationalProsodySignal) : Nat :=
  signal.questionVacuum +
  signal.ambiguityResidue +
  signal.silenceResidue +
  signal.reserveResidue

/-- Drainage/conductance supporting closure. Boundary drainage counts because
    an explicit out-of-bounds answer can close the local topology as a
    rejection. -/
def drainageCapacity (signal : ConversationalProsodySignal) : Nat :=
  signal.answerDrain +
  signal.boundaryDrain +
  signal.acceptanceCriteriaDrain +
  signal.cadenceConductance

/-- Remaining vacuum that must not be hidden by a closure claim. -/
def remainingVacuum (signal : ConversationalProsodySignal) : Nat :=
  signal.ambiguityResidue + signal.silenceResidue + signal.reserveResidue

def vacuumPressureStreamOf
    (signal : ConversationalProsodySignal) : VacuumPressureStream where
  sourceVacuum := vacuumStream signal
  conductance := drainageCapacity signal
  residue := remainingVacuum signal

/-- Finite Reynolds-style closure test:
    `conductance / (vacuum + 1) >= threshold`, expressed by multiplication. -/
def vacuumStreamClears
    (gate : ConversationalReynoldsGate)
    (signal : ConversationalProsodySignal) : Bool :=
  gate.reynoldsThreshold * (vacuumStream signal + 1) ≤
    drainageCapacity signal

def remainingVacuumClears
    (gate : ConversationalReynoldsGate)
    (signal : ConversationalProsodySignal) : Bool :=
  remainingVacuum signal ≤ gate.residualThreshold

def cadenceConductanceClears
    (gate : ConversationalReynoldsGate)
    (signal : ConversationalProsodySignal) : Bool :=
  gate.cadenceThreshold ≤ signal.cadenceConductance

/-- Full conversational prosody gate for a closure attempt. -/
def prosodyReadyToClose
    (gate : ConversationalReynoldsGate)
    (signal : ConversationalProsodySignal) : Bool :=
  vacuumStreamClears gate signal &&
  remainingVacuumClears gate signal &&
  cadenceConductanceClears gate signal

/-- Boolean mirror of the Dodgeball closure discipline, for executable routing. -/
def closureDisciplinedBool : ConversationClosure → Bool
  | .argued => true
  | .boundaryRejected => true
  | .silence => false
  | .bareTruth => false
  | .unresolved => false

/-- Thoth-facing semiotic routing decision. -/
inductive ThothSemioticMove where
  | closureFold
  | glossolaliaProbe
  | auditGap
  deriving DecidableEq, Repr

/-- If pressure is not ready, route to glossolalia/probing. If pressure is ready
    but the closure is not disciplined, preserve an audit gap. Only ready,
    disciplined closures fold. -/
def thothSemioticMove
    (gate : ConversationalReynoldsGate)
    (signal : ConversationalProsodySignal)
    (closure : ConversationClosure) : ThothSemioticMove :=
  if prosodyReadyToClose gate signal then
    if closureDisciplinedBool closure then
      .closureFold
    else
      .auditGap
  else
    .glossolaliaProbe

def addAnswerDrain
    (signal : ConversationalProsodySignal) (delta : Nat) :
    ConversationalProsodySignal :=
  { signal with answerDrain := signal.answerDrain + delta }

def addAcceptanceCriteriaDrain
    (signal : ConversationalProsodySignal) (delta : Nat) :
    ConversationalProsodySignal :=
  { signal with
      acceptanceCriteriaDrain :=
        signal.acceptanceCriteriaDrain + delta }

theorem drainage_capacity_add_answer
    (signal : ConversationalProsodySignal) (delta : Nat) :
    drainageCapacity (addAnswerDrain signal delta) =
      drainageCapacity signal + delta := by
  cases signal
  simp [drainageCapacity, addAnswerDrain, Nat.add_comm, Nat.add_left_comm]

theorem drainage_capacity_add_acceptance_criteria
    (signal : ConversationalProsodySignal) (delta : Nat) :
    drainageCapacity (addAcceptanceCriteriaDrain signal delta) =
      drainageCapacity signal + delta := by
  cases signal
  simp [drainageCapacity, addAcceptanceCriteriaDrain, Nat.add_comm,
    Nat.add_left_comm]

theorem vacuum_pressure_stream_projects
    (signal : ConversationalProsodySignal) :
    (vacuumPressureStreamOf signal).sourceVacuum = vacuumStream signal ∧
    (vacuumPressureStreamOf signal).conductance = drainageCapacity signal ∧
    (vacuumPressureStreamOf signal).residue = remainingVacuum signal := by
  exact ⟨rfl, rfl, rfl⟩

theorem prosody_ready_requires_reynolds
    {gate : ConversationalReynoldsGate}
    {signal : ConversationalProsodySignal}
    (h : prosodyReadyToClose gate signal = true) :
    vacuumStreamClears gate signal = true := by
  cases hReynolds : vacuumStreamClears gate signal with
  | false =>
      unfold prosodyReadyToClose at h
      simp [hReynolds] at h
  | true => rfl

theorem prosody_ready_requires_residual_bound
    {gate : ConversationalReynoldsGate}
    {signal : ConversationalProsodySignal}
    (h : prosodyReadyToClose gate signal = true) :
    remainingVacuumClears gate signal = true := by
  cases hReynolds : vacuumStreamClears gate signal with
  | false =>
      unfold prosodyReadyToClose at h
      simp [hReynolds] at h
  | true =>
      cases hResidual : remainingVacuumClears gate signal with
      | false =>
          unfold prosodyReadyToClose at h
          simp [hReynolds, hResidual] at h
      | true => rfl

theorem prosody_ready_requires_cadence
    {gate : ConversationalReynoldsGate}
    {signal : ConversationalProsodySignal}
    (h : prosodyReadyToClose gate signal = true) :
    cadenceConductanceClears gate signal = true := by
  cases hReynolds : vacuumStreamClears gate signal with
  | false =>
      unfold prosodyReadyToClose at h
      simp [hReynolds] at h
  | true =>
      cases hResidual : remainingVacuumClears gate signal with
      | false =>
          unfold prosodyReadyToClose at h
          simp [hReynolds, hResidual] at h
      | true =>
          cases hCadence : cadenceConductanceClears gate signal with
          | false =>
              unfold prosodyReadyToClose at h
              simp [hReynolds, hResidual, hCadence] at h
          | true => rfl

theorem silence_blocks_zero_residual_gate
    {gate : ConversationalReynoldsGate}
    {signal : ConversationalProsodySignal}
    (hGate : gate.residualThreshold = 0)
    (hSilence : 0 < signal.silenceResidue) :
    prosodyReadyToClose gate signal = false := by
  unfold prosodyReadyToClose remainingVacuumClears remainingVacuum
  have hNotReserve :
      ¬ (signal.ambiguityResidue + signal.silenceResidue +
          signal.reserveResidue ≤ gate.residualThreshold) := by
    rw [hGate]
    exact Nat.not_le_of_gt (Nat.lt_of_lt_of_le hSilence
      (Nat.le_trans
        (Nat.le_add_left signal.silenceResidue signal.ambiguityResidue)
        (Nat.le_add_right
          (signal.ambiguityResidue + signal.silenceResidue)
          signal.reserveResidue)))
  simp [hNotReserve]

theorem reserve_residue_blocks_zero_residual_gate
    {gate : ConversationalReynoldsGate}
    {signal : ConversationalProsodySignal}
    (hGate : gate.residualThreshold = 0)
    (hReserve : 0 < signal.reserveResidue) :
    prosodyReadyToClose gate signal = false := by
  unfold prosodyReadyToClose remainingVacuumClears remainingVacuum
  have hNot :
      ¬ (signal.ambiguityResidue + signal.silenceResidue +
          signal.reserveResidue ≤ gate.residualThreshold) := by
    rw [hGate]
    exact Nat.not_le_of_gt (Nat.lt_of_lt_of_le hReserve
      (Nat.le_add_left signal.reserveResidue
        (signal.ambiguityResidue + signal.silenceResidue)))
  simp [hNot]

theorem closure_disciplined_bool_iff
    (closure : ConversationClosure) :
    closureDisciplinedBool closure = true ↔ closureDiscipline closure := by
  cases closure with
  | argued =>
      simp [closureDisciplinedBool, argued_closure_has_discipline]
  | boundaryRejected =>
      simp [closureDisciplinedBool, boundary_rejection_has_discipline]
  | silence =>
      simp [closureDisciplinedBool, no_silence_closure]
  | bareTruth =>
      simp [closureDisciplinedBool, no_bare_truth_closure]
  | unresolved =>
      simp [closureDisciplinedBool, no_unresolved_closure]

theorem not_ready_routes_glossolalia
    (gate : ConversationalReynoldsGate)
    (signal : ConversationalProsodySignal)
    (closure : ConversationClosure)
    (h : prosodyReadyToClose gate signal = false) :
    thothSemioticMove gate signal closure = .glossolaliaProbe := by
  simp [thothSemioticMove, h]

theorem ready_undisciplined_routes_audit_gap
    (gate : ConversationalReynoldsGate)
    (signal : ConversationalProsodySignal)
    (closure : ConversationClosure)
    (hReady : prosodyReadyToClose gate signal = true)
    (hClosure : closureDisciplinedBool closure = false) :
    thothSemioticMove gate signal closure = .auditGap := by
  simp [thothSemioticMove, hReady, hClosure]

theorem ready_disciplined_routes_closure_fold
    (gate : ConversationalReynoldsGate)
    (signal : ConversationalProsodySignal)
    (closure : ConversationClosure)
    (hReady : prosodyReadyToClose gate signal = true)
    (hClosure : closureDisciplinedBool closure = true) :
    thothSemioticMove gate signal closure = .closureFold := by
  simp [thothSemioticMove, hReady, hClosure]

theorem closure_fold_requires_ready_and_discipline
    {gate : ConversationalReynoldsGate}
    {signal : ConversationalProsodySignal}
    {closure : ConversationClosure}
    (h : thothSemioticMove gate signal closure = .closureFold) :
    prosodyReadyToClose gate signal = true ∧
    closureDisciplinedBool closure = true := by
  unfold thothSemioticMove at h
  cases hReady : prosodyReadyToClose gate signal with
  | false =>
      simp [hReady] at h
  | true =>
      cases hClosure : closureDisciplinedBool closure with
      | false =>
          simp [hReady, hClosure] at h
      | true =>
          exact ⟨rfl, rfl⟩

theorem closure_fold_requires_closure_discipline
    {gate : ConversationalReynoldsGate}
    {signal : ConversationalProsodySignal}
    {closure : ConversationClosure}
    (h : thothSemioticMove gate signal closure = .closureFold) :
    closureDiscipline closure := by
  exact (closure_disciplined_bool_iff closure).mp
    (closure_fold_requires_ready_and_discipline h).2

/-- Canonical strict gate used by product-facing smoke certificates. -/
def canonicalConversationalGate : ConversationalReynoldsGate where
  reynoldsThreshold := 1
  residualThreshold := 0
  cadenceThreshold := 1

/-- A minimal argued answer with stable cadence and acceptance criteria clears
    the canonical gate. -/
def canonicalArguedAnswerSignal : ConversationalProsodySignal where
  questionVacuum := 0
  answerDrain := 1
  boundaryDrain := 0
  silenceResidue := 0
  ambiguityResidue := 0
  reserveResidue := 0
  cadenceConductance := 1
  acceptanceCriteriaDrain := 1

theorem canonical_argued_answer_ready :
    prosodyReadyToClose canonicalConversationalGate
      canonicalArguedAnswerSignal = true := by
  decide

theorem canonical_argued_answer_folds_for_thoth :
    thothSemioticMove canonicalConversationalGate
      canonicalArguedAnswerSignal .argued = .closureFold := by
  decide

theorem canonical_bare_truth_routes_audit_gap :
    thothSemioticMove canonicalConversationalGate
      canonicalArguedAnswerSignal .bareTruth = .auditGap := by
  decide

end ConversationalProsody
end Gnosis
