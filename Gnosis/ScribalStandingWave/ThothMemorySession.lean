import Gnosis.ScribalStandingWave.MemoryBudgetScheduler

namespace Gnosis
namespace ScribalStandingWave

structure ThothMemorySession where
  transcriptTrace : TranscriptAuditTrace
  recallView : List TranscriptRecallAtom
  scheduledMemory : ScheduledTranscriptMemory
  deriving DecidableEq, Repr

def buildThothMemorySession
    (recallPolicy : TranscriptRecallPolicy)
    (budgetPolicy : MemoryBudgetPolicy)
    (turns : List TaggedTranscriptTurn)
    (evidence : List RecallPromotionEvidence) : ThothMemorySession :=
  let trace := transcriptAuditTraceFromTurns turns
  let recalls := transcriptRecallView recallPolicy trace.atoms
  { transcriptTrace := trace
    recallView := recalls
    scheduledMemory := scheduleTranscriptMemory budgetPolicy recalls evidence }

def mergeThothMemorySession
    (recallPolicy : TranscriptRecallPolicy)
    (budgetPolicy : MemoryBudgetPolicy)
    (left right : ThothMemorySession)
    (evidence : List RecallPromotionEvidence) : ThothMemorySession :=
  let trace := mergeTranscriptAuditTrace left.transcriptTrace right.transcriptTrace
  let recalls := transcriptRecallView recallPolicy trace.atoms
  { transcriptTrace := trace
    recallView := recalls
    scheduledMemory := scheduleTranscriptMemory budgetPolicy recalls evidence }

def thothMemorySessionSound (session : ThothMemorySession) : Bool :=
  transcriptAuditTraceSound session.transcriptTrace &&
  transcriptRecallViewSound session.recallView &&
  scheduledTranscriptMemorySound session.scheduledMemory

def thothMemorySessionRejectsSourceAuthority
    (session : ThothMemorySession) : Bool :=
  session.scheduledMemory.activeMemory.all
    (fun atom => !atom.recall.claimsSourceAuthority) &&
  session.scheduledMemory.auditGaps.all
    (fun gap => !gap.claimsSourceAuthority)

def canonicalThothMemorySession : ThothMemorySession :=
  buildThothMemorySession canonicalRecallPolicy canonicalMemoryBudgetPolicy
    [canonicalTaggedTranscriptTurn, secondTaggedTranscriptTurn,
      rawEscapeTranscriptTurn]
    [freshCorroboratingEvidence]

def mergedThothMemorySession : ThothMemorySession :=
  mergeThothMemorySession canonicalRecallPolicy canonicalMemoryBudgetPolicy
    (buildThothMemorySession canonicalRecallPolicy canonicalMemoryBudgetPolicy
      [canonicalTaggedTranscriptTurn] [])
    (buildThothMemorySession canonicalRecallPolicy canonicalMemoryBudgetPolicy
      [secondTaggedTranscriptTurn, rawEscapeTranscriptTurn] [])
    [freshCorroboratingEvidence]

def authorityThothMemorySession : ThothMemorySession :=
  { canonicalThothMemorySession with
    scheduledMemory := authorityScheduledTranscriptMemory }

theorem canonical_thoth_memory_session_sound :
    thothMemorySessionSound canonicalThothMemorySession = true := by
  decide

theorem canonical_thoth_memory_session_rejects_source_authority :
    thothMemorySessionRejectsSourceAuthority canonicalThothMemorySession =
      true := by
  decide

theorem merged_thoth_memory_session_sound :
    thothMemorySessionSound mergedThothMemorySession = true := by
  decide

theorem raw_escape_remains_audit_gap_in_session :
    canonicalThothMemorySession.scheduledMemory.auditGaps.length = 1 ∧
    canonicalThothMemorySession.scheduledMemory.activeMemory.all
      (fun atom => !atom.recall.amnesiaGap) = true := by
  decide

theorem authority_thoth_memory_session_unsound :
    thothMemorySessionSound authorityThothMemorySession = false := by
  decide

end ScribalStandingWave
end Gnosis
