import Gnosis.SemanticToneWaveTabs
import Gnosis.SpeakerStandingWaveDiarization
import Gnosis.AffectStandingWaveTabs
import Gnosis.CognitiveBiasWaveTabs
import Gnosis.AestheticPoeticWaveTabs

/-
  PneumaWatermark.lean
  ====================

  Lean contract for Pneuma semantic checksums carried as bounded PCM
  standing-wave pulses.

  Runtime context:

  * `apps/pneuma-think/src/speaker-standing-wave.ts` extracts paragraph
    carriers, candidate speaker waves, and semantic tone tabs.
  * `apps/pneuma-think/src/speaker-wave-pcm.ts` maps those finite records into
    a 48 kHz mono PCM pulse train.

  This file proves only the finite contract boundary. It does not prove speaker
  identity, psychological intent, audibility, or survival through arbitrary
  hardware/codecs. A decoder must provide a received finite witness before
  channel preservation can be checked here.
-/

namespace PneumaWatermark

open SemanticToneWaveTabs
open AffectStandingWaveTabs
open CognitiveBiasWaveTabs
open AestheticPoeticWaveTabs

/-! ## Finite semantic checksum surface -/

/-- One paragraph-level pulse emitted by the Pneuma PCM encoder.

    `carrierBin` and `phaseBin` are finite bins, not real-valued frequencies.
    Runtime owns calibration from bins to hertz. -/
structure ParagraphPulse where
  paragraphIndex : Nat
  carrierBin : Nat
  phaseBin : Nat
  tone : SemanticToneKind
  confidenceBin : Nat
  deriving Repr

/-- A finite semantic checksum over the meaning-bearing transcript evidence.

    This is not a byte hash. It tracks coarse semantic and standing-wave
    evidence that may remain stable across formatting differences. -/
structure SemanticChecksum where
  paragraphCount : Nat
  speakerWaveCount : Nat
  toneEvidenceCount : Nat
  affectTabCount : Nat
  biasTabCount : Nat
  aestheticTabCount : Nat
  pulseCount : Nat
  deriving Repr

/-- The meaning-bearing packet projected into the finite watermark contract.

    Runtime may carry richer JSON evidence. This packet records only the finite
    tab witnesses that Lean can bound and project: semantic tone, affect,
    cognitive bias, and aesthetic/poetic tabs. -/
structure SemanticPacket where
  paragraphIndex : Nat
  toneTabs : List SemanticToneWaveTab
  affectTabs : List AffectStandingWaveTab
  biasTabs : List CognitiveBiasTab
  aestheticTabs : List AestheticPoeticTab
  deriving Repr

/-- Runtime-produced watermark frame before acoustic transmission. -/
structure WatermarkFrame where
  sampleRate : Nat
  carrierBaseHz : Nat
  carrierSpreadHz : Nat
  pulseSamples : Nat
  gapSamples : Nat
  speakerWaveCount : Nat
  pulses : List ParagraphPulse
  semanticPackets : List SemanticPacket
  deriving Repr

/-- A simple abstract mix certificate: the human audio and watermark frame
    share a sample rate and the mix did not clip above the declared bound. -/
structure OverlayMix where
  humanSampleRate : Nat
  watermark : WatermarkFrame
  gainNumerator : Nat
  gainDenominator : Nat
  noClipBound : Nat
  sameSampleRate : humanSampleRate = watermark.sampleRate
  positiveGainDenominator : 0 < gainDenominator
  deriving Repr

/-- Channel tolerance supplied by a concrete decoder experiment. -/
structure ChannelBound where
  maxTimingDrift : Nat
  maxCarrierBinDrift : Nat
  minRecoveredPulses : Nat
  deriving DecidableEq, Repr

/-- Number of pulse records in a frame. -/
def framePulseCount (frame : WatermarkFrame) : Nat :=
  frame.pulses.length

/-- Count tone records by pulse records for the v1 runtime encoding. -/
def frameToneEvidenceCount (frame : WatermarkFrame) : Nat :=
  (frame.semanticPackets.map (fun packet => packet.toneTabs.length)).sum

def frameAffectTabCount (frame : WatermarkFrame) : Nat :=
  (frame.semanticPackets.map (fun packet => packet.affectTabs.length)).sum

def frameBiasTabCount (frame : WatermarkFrame) : Nat :=
  (frame.semanticPackets.map (fun packet => packet.biasTabs.length)).sum

def frameAestheticTabCount (frame : WatermarkFrame) : Nat :=
  (frame.semanticPackets.map (fun packet => packet.aestheticTabs.length)).sum

/-- Semantic checksum extracted from a runtime watermark frame. -/
def checksumOfFrame (frame : WatermarkFrame) : SemanticChecksum :=
  { paragraphCount := frame.pulses.length
    speakerWaveCount := frame.speakerWaveCount
    toneEvidenceCount := frameToneEvidenceCount frame
    affectTabCount := frameAffectTabCount frame
    biasTabCount := frameBiasTabCount frame
    aestheticTabCount := frameAestheticTabCount frame
    pulseCount := framePulseCount frame }

/-- Finite Nyquist safety for the declared carrier band.

    Runtime uses hertz; Lean only checks the Nat inequality supplied in the
    frame. -/
def CarrierBandBelowNyquist (frame : WatermarkFrame) : Prop :=
  frame.carrierBaseHz + frame.carrierSpreadHz < frame.sampleRate / 2

/-- The checksum pulse count is definitionally the frame pulse count. -/
theorem checksum_pulse_count_eq_frame_count
    (frame : WatermarkFrame) :
    (checksumOfFrame frame).pulseCount = framePulseCount frame :=
  rfl

/-- The checksum paragraph count follows the same pulse list in v1 encoding. -/
theorem checksum_paragraph_count_eq_frame_count
    (frame : WatermarkFrame) :
    (checksumOfFrame frame).paragraphCount = framePulseCount frame :=
  rfl

/-- The checksum preserves the speaker-wave count supplied by runtime. -/
theorem checksum_speaker_wave_count_eq_frame
    (frame : WatermarkFrame) :
    (checksumOfFrame frame).speakerWaveCount = frame.speakerWaveCount :=
  rfl

theorem checksum_affect_tab_count_eq_frame
    (frame : WatermarkFrame) :
    (checksumOfFrame frame).affectTabCount = frameAffectTabCount frame :=
  rfl

theorem checksum_bias_tab_count_eq_frame
    (frame : WatermarkFrame) :
    (checksumOfFrame frame).biasTabCount = frameBiasTabCount frame :=
  rfl

theorem checksum_aesthetic_tab_count_eq_frame
    (frame : WatermarkFrame) :
    (checksumOfFrame frame).aestheticTabCount = frameAestheticTabCount frame :=
  rfl

/-! ## Overlay and decode contracts -/

/-- An overlay carries the same semantic checksum as its watermark component.
    This is bookkeeping: it says mixing does not rewrite the finite witness
    object before acoustic transmission. -/
def checksumOfOverlay (mix : OverlayMix) : SemanticChecksum :=
  checksumOfFrame mix.watermark

/-- Mixing under human audio preserves the finite checksum by projection to the
    watermark component. -/
theorem overlay_checksum_eq_watermark_checksum
    (mix : OverlayMix) :
    checksumOfOverlay mix = checksumOfFrame mix.watermark :=
  rfl

/-- A received frame decodes within a finite channel bound when the recovered
    pulse count clears the declared floor after timing drift allowance. -/
def DecodesWithin (source received : WatermarkFrame) (bound : ChannelBound) : Prop :=
  framePulseCount received + bound.maxTimingDrift ≥
    Nat.min (framePulseCount source) bound.minRecoveredPulses

/-- A finite broadcast certificate packages the original frame, the decoded
    frame, the channel bound, and the two proof obligations. -/
structure BroadcastCertificate where
  source : WatermarkFrame
  received : WatermarkFrame
  bound : ChannelBound
  nyquistSafe : CarrierBandBelowNyquist source
  recovered : DecodesWithin source received bound
  deriving Repr

/-- Projection theorem: a broadcast certificate provides the decode claim. -/
theorem broadcast_certificate_recovers_within_bound
    (cert : BroadcastCertificate) :
    DecodesWithin cert.source cert.received cert.bound :=
  cert.recovered

/-- Projection theorem: a broadcast certificate provides carrier-band safety. -/
theorem broadcast_certificate_carrier_safe
    (cert : BroadcastCertificate) :
    CarrierBandBelowNyquist cert.source :=
  cert.nyquistSafe

/-! ## Semantic-tone bridge -/

/-- A pulse matches a semantic tone tab when the tone kind and confidence bin
    agree at the finite boundary. Runtime may use richer evidence before it
    emits this compact pulse. -/
def PulseMatchesToneTab (pulse : ParagraphPulse) (tab : SemanticToneWaveTab) : Prop :=
  pulse.tone = tab.kind ∧ pulse.confidenceBin = tab.confidence

/-- Matching a pulse to a tab preserves the semantic tone kind. -/
theorem pulse_match_preserves_tone_kind
    {pulse : ParagraphPulse} {tab : SemanticToneWaveTab}
    (h : PulseMatchesToneTab pulse tab) :
    pulse.tone = tab.kind :=
  h.left

/-- Matching a pulse to a tab preserves the finite confidence bin. -/
theorem pulse_match_preserves_confidence
    {pulse : ParagraphPulse} {tab : SemanticToneWaveTab}
    (h : PulseMatchesToneTab pulse tab) :
    pulse.confidenceBin = tab.confidence :=
  h.right

/-! ## Rich semantic packet bridge -/

def PacketAttachedToPulse (packet : SemanticPacket) (pulse : ParagraphPulse) : Prop :=
  packet.paragraphIndex = pulse.paragraphIndex

def PacketConfidenceBoundedBy (limit : Nat) (packet : SemanticPacket) : Prop :=
  (∀ tab ∈ packet.toneTabs, tab.confidence ≤ limit) ∧
  (∀ tab ∈ packet.affectTabs, ConfidenceBoundedBy limit tab) ∧
  (∀ tab ∈ packet.biasTabs, BiasBoundedBy limit tab) ∧
  (∀ tab ∈ packet.aestheticTabs, AestheticBoundedBy limit tab)

def PacketProjectsLeanCatalog (packet : SemanticPacket) : Prop :=
  ∀ tab ∈ packet.affectTabs, TabMatchesLeanCatalog tab

def PacketCarriesSemanticDimensions (packet : SemanticPacket) : Prop :=
  0 < packet.toneTabs.length + packet.affectTabs.length +
    packet.biasTabs.length + packet.aestheticTabs.length

def SafeSemanticPacketProjection
    (limit : Nat) (packet : SemanticPacket) (pulse : ParagraphPulse) : Prop :=
  PacketAttachedToPulse packet pulse ∧ PacketConfidenceBoundedBy limit packet ∧
  PacketProjectsLeanCatalog packet

theorem safe_packet_projection_projects_attachment
    (limit : Nat) (packet : SemanticPacket) (pulse : ParagraphPulse)
    (h : SafeSemanticPacketProjection limit packet pulse) :
    PacketAttachedToPulse packet pulse :=
  h.1

theorem safe_packet_projection_projects_affect_catalog
    (limit : Nat) (packet : SemanticPacket) (pulse : ParagraphPulse)
    (h : SafeSemanticPacketProjection limit packet pulse) :
    PacketProjectsLeanCatalog packet :=
  h.2.2

theorem packet_carries_dimensions_from_affect
    (packet : SemanticPacket) (tab : AffectStandingWaveTab)
    (h : tab ∈ packet.affectTabs) :
    PacketCarriesSemanticDimensions packet := by
  unfold PacketCarriesSemanticDimensions
  have hpos : 0 < packet.affectTabs.length := List.length_pos_of_mem h
  calc 0
      < packet.affectTabs.length := hpos
    _ ≤ packet.toneTabs.length + packet.affectTabs.length := Nat.le_add_left _ _
    _ ≤ (packet.toneTabs.length + packet.affectTabs.length) + packet.biasTabs.length := Nat.le_add_right _ _
    _ ≤ ((packet.toneTabs.length + packet.affectTabs.length) + packet.biasTabs.length) + packet.aestheticTabs.length := Nat.le_add_right _ _

/-! ## Pure symbolic encode/decode round trip -/

/-- Symbolic pulse code used as the lossless target beneath PCM calibration.

    Runtime PCM is analog/digital signal data. This symbolic layer is the
    finite object the decoder is supposed to recover before channel drift is
    considered. -/
structure EncodedPulse where
  indexCode : Nat
  carrierCode : Nat
  phaseCode : Nat
  toneCode : SemanticToneKind
  confidenceCode : Nat
  deriving DecidableEq, Repr

/-- Lossless symbolic encoder for one paragraph pulse. -/
def encodePulse (pulse : ParagraphPulse) : EncodedPulse :=
  { indexCode := pulse.paragraphIndex
    carrierCode := pulse.carrierBin
    phaseCode := pulse.phaseBin
    toneCode := pulse.tone
    confidenceCode := pulse.confidenceBin }

/-- Lossless symbolic decoder for one paragraph pulse. -/
def decodePulse (code : EncodedPulse) : ParagraphPulse :=
  { paragraphIndex := code.indexCode
    carrierBin := code.carrierCode
    phaseBin := code.phaseCode
    tone := code.toneCode
    confidenceBin := code.confidenceCode }

/-- Encode a finite pulse list without adding timing or carrier drift. -/
def encodePulseList : List ParagraphPulse → List EncodedPulse
  | [] => []
  | pulse :: rest => encodePulse pulse :: encodePulseList rest

/-- Decode a finite pulse list from the symbolic lossless code. -/
def decodePulseList : List EncodedPulse → List ParagraphPulse
  | [] => []
  | code :: rest => decodePulse code :: decodePulseList rest

/-- One-pulse symbolic encode/decode is definitionally identity. -/
theorem decode_encode_pulse_id
    (pulse : ParagraphPulse) :
    decodePulse (encodePulse pulse) = pulse := by
  cases pulse
  rfl

/-- Symbolic encode/decode preserves finite pulse lists exactly. -/
theorem decode_encode_pulse_list_id
    (pulses : List ParagraphPulse) :
    decodePulseList (encodePulseList pulses) = pulses := by
  induction pulses with
  | nil =>
      rfl
  | cons pulse rest ih =>
      unfold encodePulseList
      unfold decodePulseList
      rw [decode_encode_pulse_id pulse]
      rw [ih]

/-- Symbolic encoding preserves pulse-list length. -/
theorem encode_pulse_list_length_eq
    (pulses : List ParagraphPulse) :
    (encodePulseList pulses).length = pulses.length := by
  induction pulses with
  | nil =>
      rfl
  | cons pulse rest ih =>
      unfold encodePulseList
      change Nat.succ (encodePulseList rest).length = Nat.succ rest.length
      rw [ih]

/-- Symbolic decoding preserves encoded-list length. -/
theorem decode_pulse_list_length_eq
    (codes : List EncodedPulse) :
    (decodePulseList codes).length = codes.length := by
  induction codes with
  | nil =>
      rfl
  | cons code rest ih =>
      unfold decodePulseList
      change Nat.succ (decodePulseList rest).length = Nat.succ rest.length
      rw [ih]

/-- A frame encoded and immediately decoded through the symbolic layer keeps
    its pulse count. -/
theorem symbolic_round_trip_preserves_frame_pulse_count
    (frame : WatermarkFrame) :
    (decodePulseList (encodePulseList frame.pulses)).length = framePulseCount frame := by
  rw [decode_encode_pulse_list_id frame.pulses]
  rfl

end PneumaWatermark
