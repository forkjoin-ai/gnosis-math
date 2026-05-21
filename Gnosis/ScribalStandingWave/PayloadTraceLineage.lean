import Gnosis.ScribalStandingWave

namespace Gnosis
namespace ScribalStandingWave

/-- A payload trace keeps the generated-content fingerprints visible for audit,
    while trace soundness remains reducible to the folded child envelopes. -/
structure BodyPolitickPayloadTrace where
  trace : ScribalAuditTrace
  payloadHashes : List Nat
  deriving DecidableEq, Repr

def foldBodyPolitickPayloadTrace
    (left right : BodyPolitickScribalPayload) : BodyPolitickPayloadTrace where
  trace := foldBodyPolitickPayloadThothMemory left right
  payloadHashes := [left.generatedTextHash, right.generatedTextHash]

def payloadTraceHashesPreserved
    (payloadTrace : BodyPolitickPayloadTrace)
    (left right : BodyPolitickScribalPayload) : Bool :=
  payloadTrace.payloadHashes = [left.generatedTextHash, right.generatedTextHash]

def payloadTraceAuthorityReducedToTrace
    (payloadTrace : BodyPolitickPayloadTrace) : Bool :=
  payloadTrace.trace.claimsSourceAuthority = false

def payloadTraceLineageReducedToTrace
    (payloadTrace : BodyPolitickPayloadTrace) : Bool :=
  auditTraceHasTheoremLineage payloadTrace.trace

def bodyPolitickPayloadTraceSound
    (payloadTrace : BodyPolitickPayloadTrace) : Bool :=
  scribalAuditTraceSound payloadTrace.trace &&
  payloadTraceAuthorityReducedToTrace payloadTrace &&
  payloadTraceLineageReducedToTrace payloadTrace

def canonicalBodyPolitickPayloadTrace : BodyPolitickPayloadTrace :=
  foldBodyPolitickPayloadTrace canonicalBodyPolitickScribalPayload
    alternateObservedContentBodyPolitickScribalPayload

def droppedPayloadHashBodyPolitickPayloadTrace : BodyPolitickPayloadTrace :=
  { canonicalBodyPolitickPayloadTrace with payloadHashes := [17321] }

def sourceAuthorityBodyPolitickPayloadTrace : BodyPolitickPayloadTrace :=
  { canonicalBodyPolitickPayloadTrace with
    trace := sourceAuthorityAuditTrace }

theorem canonical_body_politick_payload_trace_sound :
    bodyPolitickPayloadTraceSound canonicalBodyPolitickPayloadTrace = true := by
  decide

theorem canonical_body_politick_payload_trace_preserves_hashes :
    payloadTraceHashesPreserved canonicalBodyPolitickPayloadTrace
      canonicalBodyPolitickScribalPayload
      alternateObservedContentBodyPolitickScribalPayload = true := by
  decide

theorem dropped_payload_hash_trace_fails_hash_preservation :
    payloadTraceHashesPreserved droppedPayloadHashBodyPolitickPayloadTrace
      canonicalBodyPolitickScribalPayload
      alternateObservedContentBodyPolitickScribalPayload = false := by
  decide

theorem source_authority_payload_trace_unsound :
    bodyPolitickPayloadTraceSound sourceAuthorityBodyPolitickPayloadTrace =
      false := by
  decide

end ScribalStandingWave
end Gnosis
