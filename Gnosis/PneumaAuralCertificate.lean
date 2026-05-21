import Gnosis.PneumaWatermark
import Gnosis.UniversalStandingWaveTheorem

/-
  PneumaAuralCertificate.lean
  ===========================

  Finite Lean bridge for the runtime aural certificate pipeline.

  The runtime object lives in `apps/pneuma-think/src/aural-certificate.ts`.
  This file records the formal boundary: transcript tags/turns provide the
  semantic witness; watermark pulses provide the machine-readable acoustic
  packet; the certificate connects their finite counts and checksums.
-/

namespace Gnosis
namespace PneumaAuralCertificate

open SpeakerStandingWaveDiarization
open Gnosis.UniversalStandingWaveTheorem
open PneumaWatermark

/-- A runtime aural certificate pairs a transcript certificate with the
    watermark frame emitted over PCM. -/
structure AuralCertificate where
  transcript : TranscriptStandingWaveCertificate
  watermark : WatermarkFrame
  checksum : SemanticChecksum
  confidenceLimit : Nat
  transcriptAdmissible : TranscriptCertificateAdmissible confidenceLimit transcript
  checksumProjects : checksum = checksumOfFrame watermark
  pulseCountMatchesTags : framePulseCount watermark = transcript.tags.length
  deriving Repr

/-- Projection: the aural certificate carries the same checksum as its
    watermark frame. -/
theorem aural_certificate_checksum_projects_to_watermark
    (cert : AuralCertificate) :
    cert.checksum = checksumOfFrame cert.watermark :=
  cert.checksumProjects

/-- Projection: every admitted aural certificate inherits transcript tag
    coverage over turn spans. -/
theorem aural_certificate_tags_cover_turns
    (cert : AuralCertificate) :
    TagsCoverTurns cert.transcript.tags cert.transcript.turns :=
  cert.transcriptAdmissible.2.1

/-- Projection: every admitted aural certificate inherits bounded transcript
    tag confidence values. -/
theorem aural_certificate_well_formed_tags
    (cert : AuralCertificate) :
    WellFormedTranscriptTags cert.confidenceLimit cert.transcript.tags :=
  cert.transcriptAdmissible.2.2

/-- Projection: the watermark pulse count is synchronized to the transcript tag
    count. Runtime decode reports compare the recovered pulse checksum against
    this finite target. -/
theorem aural_certificate_pulse_count_matches_tags
    (cert : AuralCertificate) :
    framePulseCount cert.watermark = cert.transcript.tags.length :=
  cert.pulseCountMatchesTags

/-- If a certificate is admissible, the encoded transcript tags project back to
    the carriers consumed by the standing-wave diarizer. -/
theorem aural_certificate_tags_project_to_carriers
    (cert : AuralCertificate) :
    cert.transcript.tags.map (fun tag => tag.carrier) = cert.transcript.carriers :=
  transcript_certificate_tags_project_to_carriers cert.confidenceLimit cert.transcript cert.transcriptAdmissible

end PneumaAuralCertificate
end Gnosis
