import Gnosis.ScribalStandingWave.ThothMemorySession

namespace Gnosis
namespace ScribalStandingWave

structure ThothTranscriptInput where
  turn : TranscriptTurn
  rawEscapeRequested : Bool
  deriving DecidableEq, Repr

def thothTranscriptInputToTaggedTurn
    (input : ThothTranscriptInput) : TaggedTranscriptTurn :=
  if input.rawEscapeRequested then
    tagTranscriptTurn input.turn TaggedTranscriptMode.rawEscape
  else
    tagTranscriptTurn input.turn

structure ThothMemoryAdapter where
  session : ThothMemorySession
  generationContext : List ScheduledMemoryAtom
  auditGaps : List TranscriptRecallAtom
  rawEscapeRequired : Bool
  deriving DecidableEq, Repr

structure ThothConsumedMemoryContext where
  activeContext : List ScheduledMemoryAtom
  visibleAuditGaps : List TranscriptRecallAtom
  sourceAuthorityRejected : Bool
  deriving DecidableEq, Repr

def buildThothMemoryAdapter
    (recallPolicy : TranscriptRecallPolicy)
    (budgetPolicy : MemoryBudgetPolicy)
    (inputs : List ThothTranscriptInput)
    (evidence : List RecallPromotionEvidence) : ThothMemoryAdapter :=
  let turns := inputs.map thothTranscriptInputToTaggedTurn
  let session := buildThothMemorySession recallPolicy budgetPolicy turns evidence
  { session := session
    generationContext := session.scheduledMemory.activeMemory
    auditGaps := session.scheduledMemory.auditGaps
    rawEscapeRequired := inputs.any (fun input => input.rawEscapeRequested) }

def thothMemoryAdapterSound (adapter : ThothMemoryAdapter) : Bool :=
  thothMemorySessionSound adapter.session &&
  thothMemorySessionRejectsSourceAuthority adapter.session &&
  adapter.generationContext.all (fun atom =>
    transcriptRecallAtomSound atom.recall &&
    !atom.recall.amnesiaGap &&
    !atom.recall.claimsSourceAuthority) &&
  adapter.auditGaps.all (fun gap =>
    gap.amnesiaGap && !gap.claimsSourceAuthority)

def consumeThothMemoryAdapter
    (adapter : ThothMemoryAdapter) : ThothConsumedMemoryContext :=
  { activeContext := adapter.generationContext
    visibleAuditGaps := adapter.auditGaps
    sourceAuthorityRejected :=
      adapter.generationContext.all
        (fun atom => !atom.recall.claimsSourceAuthority) &&
      adapter.auditGaps.all (fun gap => !gap.claimsSourceAuthority) }

def thothConsumedMemoryContextSound
    (context : ThothConsumedMemoryContext) : Bool :=
  context.sourceAuthorityRejected &&
  context.activeContext.all (fun atom =>
    transcriptRecallAtomSound atom.recall &&
    !atom.recall.amnesiaGap &&
    !atom.recall.claimsSourceAuthority) &&
  context.visibleAuditGaps.all (fun gap =>
    gap.amnesiaGap && !gap.claimsSourceAuthority)

def canonicalThothTranscriptInput : ThothTranscriptInput where
  turn := canonicalTranscriptTurn
  rawEscapeRequested := false

def rawEscapeThothTranscriptInput : ThothTranscriptInput where
  turn := secondTranscriptTurn
  rawEscapeRequested := true

def canonicalThothMemoryAdapter : ThothMemoryAdapter :=
  buildThothMemoryAdapter canonicalRecallPolicy canonicalMemoryBudgetPolicy
    [canonicalThothTranscriptInput, rawEscapeThothTranscriptInput]
    [freshCorroboratingEvidence]

def authorityThothMemoryAdapter : ThothMemoryAdapter :=
  { canonicalThothMemoryAdapter with
    generationContext :=
      canonicalThothMemoryAdapter.generationContext.map
        (fun atom =>
          { atom with recall :=
              { atom.recall with claimsSourceAuthority := true } }) }

def canonicalThothConsumedMemoryContext : ThothConsumedMemoryContext :=
  consumeThothMemoryAdapter canonicalThothMemoryAdapter

def authorityThothConsumedMemoryContext : ThothConsumedMemoryContext :=
  consumeThothMemoryAdapter authorityThothMemoryAdapter

theorem default_thoth_input_maps_to_tagged_turn :
    (thothTranscriptInputToTaggedTurn canonicalThothTranscriptInput).mode =
      TaggedTranscriptMode.tagged := by
  decide

theorem raw_thoth_input_maps_to_raw_escape :
    (thothTranscriptInputToTaggedTurn rawEscapeThothTranscriptInput).mode =
      TaggedTranscriptMode.rawEscape := by
  decide

theorem canonical_thoth_memory_adapter_sound :
    thothMemoryAdapterSound canonicalThothMemoryAdapter = true := by
  decide

theorem thoth_adapter_generation_context_has_no_amnesia_gaps :
    canonicalThothMemoryAdapter.generationContext.all
      (fun atom => !atom.recall.amnesiaGap) = true := by
  decide

theorem thoth_adapter_preserves_raw_escape_as_audit_gap :
    canonicalThothMemoryAdapter.rawEscapeRequired = true ∧
    canonicalThothMemoryAdapter.auditGaps.length = 1 := by
  decide

theorem authority_thoth_memory_adapter_unsound :
    thothMemoryAdapterSound authorityThothMemoryAdapter = false := by
  decide

theorem canonical_consumed_thoth_memory_context_sound :
    thothConsumedMemoryContextSound canonicalThothConsumedMemoryContext =
      true := by
  decide

theorem consumed_thoth_memory_context_has_no_amnesia_active_context :
    canonicalThothConsumedMemoryContext.activeContext.all
      (fun atom => !atom.recall.amnesiaGap) = true := by
  decide

theorem consumed_thoth_memory_context_preserves_visible_audit_gaps :
    canonicalThothConsumedMemoryContext.visibleAuditGaps.length = 1 := by
  decide

theorem authority_consumed_thoth_memory_context_unsound :
    thothConsumedMemoryContextSound authorityThothConsumedMemoryContext =
      false := by
  decide

end ScribalStandingWave
end Gnosis
