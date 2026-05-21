import Gnosis.ScribalStandingWave.TaggedTranscriptMode

namespace Gnosis
namespace ScribalStandingWave

structure TranscriptAuditAtom where
  turnIndex : Nat
  contentHash : Nat
  mode : TaggedTranscriptMode
  auditTagPresent : Bool
  escapeGap : Bool
  claimsSourceAuthority : Bool
  deriving DecidableEq, Repr

def transcriptAuditAtomFromTurn
    (turn : TaggedTranscriptTurn) : TranscriptAuditAtom where
  turnIndex := turn.turn.turnIndex
  contentHash := turn.turn.contentHash
  mode := turn.mode
  auditTagPresent := turn.auditTagPresent
  escapeGap := turn.mode = TaggedTranscriptMode.rawEscape
  claimsSourceAuthority := turn.claimsSourceAuthority

def transcriptAuditAtomSound (atom : TranscriptAuditAtom) : Bool :=
  match atom.mode with
  | TaggedTranscriptMode.tagged =>
      atom.auditTagPresent &&
      !atom.escapeGap &&
      !atom.claimsSourceAuthority
  | TaggedTranscriptMode.rawEscape =>
      !atom.auditTagPresent &&
      atom.escapeGap &&
      !atom.claimsSourceAuthority

def transcriptAuditAtomPresent
    (atom : TranscriptAuditAtom) (atoms : List TranscriptAuditAtom) : Bool :=
  atoms.any (fun candidate => candidate = atom)

def transcriptAuditJoin
    (left right : List TranscriptAuditAtom) : List TranscriptAuditAtom :=
  left ++ right.filter (fun atom => !transcriptAuditAtomPresent atom left)

def transcriptAuditAtomsSound (atoms : List TranscriptAuditAtom) : Bool :=
  atoms.all transcriptAuditAtomSound

def transcriptAuditTurnsCovered
    (turns : List TaggedTranscriptTurn)
    (atoms : List TranscriptAuditAtom) : Bool :=
  turns.all (fun turn =>
    transcriptAuditAtomPresent (transcriptAuditAtomFromTurn turn) atoms)

def transcriptAuditRawEscapesVisible (atoms : List TranscriptAuditAtom) : Bool :=
  atoms.all (fun atom =>
    if atom.mode = TaggedTranscriptMode.rawEscape then atom.escapeGap else true)

structure TranscriptAuditTrace where
  turns : List TaggedTranscriptTurn
  atoms : List TranscriptAuditAtom
  deriving DecidableEq, Repr

def transcriptAuditTraceSound (trace : TranscriptAuditTrace) : Bool :=
  transcriptAuditAtomsSound trace.atoms &&
  transcriptAuditTurnsCovered trace.turns trace.atoms &&
  transcriptAuditRawEscapesVisible trace.atoms

def transcriptAuditTraceFromTurns
    (turns : List TaggedTranscriptTurn) : TranscriptAuditTrace where
  turns := turns
  atoms := turns.map transcriptAuditAtomFromTurn

def mergeTranscriptAuditTrace
    (left right : TranscriptAuditTrace) : TranscriptAuditTrace where
  turns := left.turns ++
    right.turns.filter (fun turn =>
      !transcriptAuditAtomPresent (transcriptAuditAtomFromTurn turn)
        (left.turns.map transcriptAuditAtomFromTurn))
  atoms := transcriptAuditJoin left.atoms right.atoms

def secondTranscriptTurn : TranscriptTurn where
  turnIndex := 1
  contentHash := 88421

def secondTaggedTranscriptTurn : TaggedTranscriptTurn :=
  tagTranscriptTurn secondTranscriptTurn

def canonicalTranscriptAuditTrace : TranscriptAuditTrace :=
  transcriptAuditTraceFromTurns
    [canonicalTaggedTranscriptTurn, secondTaggedTranscriptTurn]

def rawGapTranscriptAuditTrace : TranscriptAuditTrace :=
  transcriptAuditTraceFromTurns
    [canonicalTaggedTranscriptTurn, rawEscapeTranscriptTurn]

def mergedTranscriptAuditTrace : TranscriptAuditTrace :=
  mergeTranscriptAuditTrace
    (transcriptAuditTraceFromTurns [canonicalTaggedTranscriptTurn])
    (transcriptAuditTraceFromTurns
      [canonicalTaggedTranscriptTurn, secondTaggedTranscriptTurn])

def authorityTranscriptAuditTrace : TranscriptAuditTrace :=
  transcriptAuditTraceFromTurns [sourceAuthorityTaggedTranscriptTurn]

theorem canonical_transcript_audit_trace_sound :
    transcriptAuditTraceSound canonicalTranscriptAuditTrace = true := by
  decide

theorem raw_gap_transcript_audit_trace_sound :
    transcriptAuditTraceSound rawGapTranscriptAuditTrace = true := by
  decide

theorem merged_transcript_audit_trace_sound :
    transcriptAuditTraceSound mergedTranscriptAuditTrace = true := by
  decide

theorem transcript_audit_join_preserves_left_atom :
    transcriptAuditAtomPresent
      (transcriptAuditAtomFromTurn canonicalTaggedTranscriptTurn)
      (transcriptAuditJoin
        [transcriptAuditAtomFromTurn canonicalTaggedTranscriptTurn]
        [transcriptAuditAtomFromTurn secondTaggedTranscriptTurn]) = true := by
  decide

theorem transcript_audit_join_preserves_right_atom :
    transcriptAuditAtomPresent
      (transcriptAuditAtomFromTurn secondTaggedTranscriptTurn)
      (transcriptAuditJoin
        [transcriptAuditAtomFromTurn canonicalTaggedTranscriptTurn]
        [transcriptAuditAtomFromTurn secondTaggedTranscriptTurn]) = true := by
  decide

theorem transcript_audit_join_idempotent_on_canonical_atom :
    transcriptAuditJoin
      [transcriptAuditAtomFromTurn canonicalTaggedTranscriptTurn]
      [transcriptAuditAtomFromTurn canonicalTaggedTranscriptTurn] =
      [transcriptAuditAtomFromTurn canonicalTaggedTranscriptTurn] := by
  decide

theorem authority_transcript_audit_trace_unsound :
    transcriptAuditTraceSound authorityTranscriptAuditTrace = false := by
  decide

end ScribalStandingWave
end Gnosis
