import Gnosis.PneumaWatermark
import Gnosis.SpeakerStandingWaveDiarization

/-
  PneumaCrossWireTranscript.lean
  =================================

  Finite bridge for carrying Pneuma transcript certificates across Bitwise,
  Aeon Flow, Dash FlowFrame storage/sync, and DashRelay relay surfaces.

  The theorem surface is deliberately modest: it proves packet bookkeeping,
  checksum projection, explicit raw-audit gaps, and non-authority of relay or
  storage wrappers. It does not prove speaker identity, intent, culture,
  diagnosis, or preservation through arbitrary audio/network channels.
-/

namespace PneumaCrossWireTranscript

open PneumaWatermark

inductive PneumaCodecKind where
  | raw
  | phonemeV1
  | prosodyV1
  | voiceFlacV1
  deriving DecidableEq, Repr

inductive PneumaDirection where
  | input
  | output
  | internal
  deriving DecidableEq, Repr

inductive PneumaFrameRole where
  | body
  | consciousness
  deriving DecidableEq, Repr

inductive PneumaTranscriptMode where
  | tagged
  | debug
  | raw
  deriving DecidableEq, Repr

inductive PneumaWireSurface where
  | bitwise
  | aeonFlow
  | dashFlowFrame
  | dashRelay
  deriving DecidableEq, Repr

structure ConfidenceSummary where
  min : Nat
  mean : Nat
  max : Nat
  lowConfidenceCount : Nat
  deriving DecidableEq, Repr

structure PneumaTranscriptPacket where
  codec : PneumaCodecKind
  direction : PneumaDirection
  role : PneumaFrameRole
  mode : PneumaTranscriptMode
  transcriptChecksum : Nat
  tagChecksum : Nat
  packetCount : Nat
  semanticChecksum : SemanticChecksum
  confidence : ConfidenceSummary
  tagsCoverTurns : Bool
  wellFormedTags : Bool
  deriving Repr

structure CrossWireFrame where
  surface : PneumaWireSurface
  streamId : Nat
  sequence : Nat
  vented : Bool
  finished : Bool
  packet : PneumaTranscriptPacket
  claimsAuthority : Bool
  deriving Repr

def CodecKindFinite (_codec : PneumaCodecKind) : Prop :=
  True

def IsRawAuditGap (packet : PneumaTranscriptPacket) : Prop :=
  packet.codec = .raw ∨ packet.mode = .raw

def PacketChecksumProjection (packet : PneumaTranscriptPacket) : Nat :=
  packet.transcriptChecksum + packet.tagChecksum + packet.packetCount +
    packet.semanticChecksum.pulseCount + packet.semanticChecksum.affectTabCount +
    packet.semanticChecksum.biasTabCount + packet.semanticChecksum.aestheticTabCount

def FrameChecksumProjection (frame : CrossWireFrame) : Nat :=
  PacketChecksumProjection frame.packet

def TagsSurviveWireWrap (frame : CrossWireFrame) : Prop :=
  frame.packet.tagsCoverTurns = true ∧ frame.packet.wellFormedTags = true

def WireWrapperNonAuthority (frame : CrossWireFrame) : Prop :=
  frame.claimsAuthority = false

def SafeCrossWirePacket (frame : CrossWireFrame) : Prop :=
  CodecKindFinite frame.packet.codec ∧
  WireWrapperNonAuthority frame ∧
  (IsRawAuditGap frame.packet → frame.vented = true) ∧
  TagsSurviveWireWrap frame

theorem codec_kind_finite (codec : PneumaCodecKind) :
    CodecKindFinite codec := by
  trivial

theorem frame_checksum_projects_packet
    (frame : CrossWireFrame) :
    FrameChecksumProjection frame = PacketChecksumProjection frame.packet :=
  rfl

theorem frame_projects_semantic_checksum
    (frame : CrossWireFrame) :
    frame.packet.semanticChecksum = frame.packet.semanticChecksum :=
  rfl

theorem safe_cross_wire_projects_non_authority
    {frame : CrossWireFrame}
    (h : SafeCrossWirePacket frame) :
    WireWrapperNonAuthority frame :=
  h.2.1

theorem safe_cross_wire_projects_tag_coverage
    {frame : CrossWireFrame}
    (h : SafeCrossWirePacket frame) :
    TagsSurviveWireWrap frame :=
  h.2.2.2

theorem safe_cross_wire_raw_gap_is_vented
    {frame : CrossWireFrame}
    (h : SafeCrossWirePacket frame)
    (hRaw : IsRawAuditGap frame.packet) :
    frame.vented = true :=
  h.2.2.1 hRaw

def sampleConfidence : ConfidenceSummary :=
  { min := 58, mean := 72, max := 91, lowConfidenceCount := 1 }

def samplePacket : PneumaTranscriptPacket :=
  { codec := .phonemeV1
    direction := .input
    role := .body
    mode := .tagged
    transcriptChecksum := 101
    tagChecksum := 202
    packetCount := 1
    semanticChecksum :=
      { paragraphCount := 1
        speakerWaveCount := 1
        toneEvidenceCount := 1
        affectTabCount := 1
        biasTabCount := 0
        aestheticTabCount := 1
        pulseCount := 1 }
    confidence := sampleConfidence
    tagsCoverTurns := true
    wellFormedTags := true }

def sampleFrame : CrossWireFrame :=
  { surface := .aeonFlow
    streamId := 2000
    sequence := 0
    vented := false
    finished := false
    packet := samplePacket
    claimsAuthority := false }

theorem sample_frame_safe : SafeCrossWirePacket sampleFrame := by
  constructor
  · trivial
  constructor
  · rfl
  constructor
  · intro hRaw
    cases hRaw with
    | inl hCodec => cases hCodec
    | inr hMode => cases hMode
  · constructor <;> rfl

def sampleRawPacket : PneumaTranscriptPacket :=
  { samplePacket with codec := .raw, mode := .raw }

def sampleRawAuditFrame : CrossWireFrame :=
  { sampleFrame with packet := sampleRawPacket, vented := true }

theorem sample_raw_audit_frame_safe : SafeCrossWirePacket sampleRawAuditFrame := by
  constructor
  · trivial
  constructor
  · rfl
  constructor
  · intro _hRaw
    rfl
  · constructor <;> rfl

end PneumaCrossWireTranscript
