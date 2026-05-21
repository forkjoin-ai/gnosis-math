import Gnosis.ScribalStandingWave

namespace Gnosis
namespace ScribalStandingWave

inductive TaggedTranscriptMode where
  | tagged
  | rawEscape
  deriving DecidableEq, Repr

def defaultTaggedTranscriptMode : TaggedTranscriptMode :=
  TaggedTranscriptMode.tagged

structure TranscriptTurn where
  turnIndex : Nat
  contentHash : Nat
  deriving DecidableEq, Repr

structure TaggedTranscriptTurn where
  turn : TranscriptTurn
  mode : TaggedTranscriptMode
  envelope : ScribalResponseEnvelope
  auditTagPresent : Bool
  escapeHatchAcknowledged : Bool
  claimsSourceAuthority : Bool
  deriving DecidableEq, Repr

def taggedTranscriptTurnSound (turn : TaggedTranscriptTurn) : Bool :=
  match turn.mode with
  | TaggedTranscriptMode.tagged =>
      turn.auditTagPresent &&
      !turn.escapeHatchAcknowledged &&
      scribalResponseEnvelopeSound turn.envelope &&
      !turn.claimsSourceAuthority
  | TaggedTranscriptMode.rawEscape =>
      !turn.auditTagPresent &&
      turn.escapeHatchAcknowledged &&
      !turn.claimsSourceAuthority

def tagTranscriptTurn
    (turn : TranscriptTurn)
    (mode : TaggedTranscriptMode := defaultTaggedTranscriptMode) :
    TaggedTranscriptTurn :=
  match mode with
  | TaggedTranscriptMode.tagged =>
      { turn := turn
        mode := TaggedTranscriptMode.tagged
        envelope := canonicalScribalResponseEnvelope
        auditTagPresent := true
        escapeHatchAcknowledged := false
        claimsSourceAuthority := false }
  | TaggedTranscriptMode.rawEscape =>
      { turn := turn
        mode := TaggedTranscriptMode.rawEscape
        envelope := canonicalScribalResponseEnvelope
        auditTagPresent := false
        escapeHatchAcknowledged := true
        claimsSourceAuthority := false }

def canonicalTranscriptTurn : TranscriptTurn where
  turnIndex := 0
  contentHash := 17321

def canonicalTaggedTranscriptTurn : TaggedTranscriptTurn :=
  tagTranscriptTurn canonicalTranscriptTurn

def rawEscapeTranscriptTurn : TaggedTranscriptTurn :=
  tagTranscriptTurn canonicalTranscriptTurn TaggedTranscriptMode.rawEscape

def sourceAuthorityTaggedTranscriptTurn : TaggedTranscriptTurn :=
  { canonicalTaggedTranscriptTurn with claimsSourceAuthority := true }

def missingAuditTagTranscriptTurn : TaggedTranscriptTurn :=
  { canonicalTaggedTranscriptTurn with auditTagPresent := false }

def unacknowledgedRawEscapeTranscriptTurn : TaggedTranscriptTurn :=
  { rawEscapeTranscriptTurn with escapeHatchAcknowledged := false }

theorem default_transcript_mode_is_tagged :
    defaultTaggedTranscriptMode = TaggedTranscriptMode.tagged := by
  rfl

theorem canonical_tagged_transcript_turn_sound :
    taggedTranscriptTurnSound canonicalTaggedTranscriptTurn = true := by
  decide

theorem raw_escape_transcript_turn_sound_without_source_authority :
    taggedTranscriptTurnSound rawEscapeTranscriptTurn = true := by
  decide

theorem source_authority_tagged_transcript_turn_unsound :
    taggedTranscriptTurnSound sourceAuthorityTaggedTranscriptTurn = false := by
  decide

theorem missing_audit_tag_transcript_turn_unsound :
    taggedTranscriptTurnSound missingAuditTagTranscriptTurn = false := by
  decide

theorem unacknowledged_raw_escape_transcript_turn_unsound :
    taggedTranscriptTurnSound unacknowledgedRawEscapeTranscriptTurn = false := by
  decide

end ScribalStandingWave
end Gnosis
