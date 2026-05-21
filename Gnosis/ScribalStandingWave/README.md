# Scribal Standing Wave

Parent: [Gnosis](../README.md)

Companion modules for the finite Thoth scribal mechanics kernel in
[`../ScribalStandingWave.lean`](../ScribalStandingWave.lean).

## Modules

- [PayloadTraceLineage.lean](./PayloadTraceLineage.lean) - payload-trace
  lineage contract for Body Politick-derived Thoth memory. Generated-content
  hashes are preserved as observations, while authority and theorem lineage
  remain reducible to folded child envelopes.
- [TaggedTranscriptMode.lean](./TaggedTranscriptMode.lean) - default tagged
  transcript mode contract with an explicit raw escape hatch that remains
  non-authoritative.
- [TranscriptAuditTrace.lean](./TranscriptAuditTrace.lean) - CRDT-shaped
  transcript audit memory: tagged turns and raw escape gaps merge
  monotonically as audit atoms, with deterministic turn identity and no source
  authority claim.
- [TranscriptCrdtLaws.lean](./TranscriptCrdtLaws.lean) - canonicalized CRDT
  laws for transcript audit atoms: idempotence, commutativity, associativity,
  and raw-gap preservation over normalized audit memory.
- [TranscriptDampeningAmnesia.lean](./TranscriptDampeningAmnesia.lean) -
  bounded recall view over transcript audit atoms. Durable atoms remain in the
  CRDT log, while old tagged turns are dampened and raw escapes become explicit
  amnesia gaps.
- [RecallPromotionGate.lean](./RecallPromotionGate.lean) - promotion gate for
  dampened transcript recall. Only fresh tagged corroboration over the same
  content can restore full active weight; amnesia gaps remain non-promotable.
- [MemoryBudgetScheduler.lean](./MemoryBudgetScheduler.lean) - finite
  active-memory scheduler. Promoted fresh tagged atoms rank first, active atoms
  rank second, dampened atoms remain eligible when budget permits, and amnesia
  gaps stay audit-visible outside active context.
- [ThothMemorySession.lean](./ThothMemorySession.lean) - product session
  wrapper from tagged turns through CRDT audit trace, recall view, promotion,
  and scheduled active memory, preserving the non-authority invariant after
  merges and raw escapes.
- [ThothMemoryAdapter.lean](./ThothMemoryAdapter.lean) - Thoth-facing adapter
  contract: transcript inputs are tagged by default, raw escape requires an
  explicit request, active generation context comes only from scheduled recall,
  raw escapes stay visible as audit gaps, and consumed Thoth context is checked
  again before a responder can use it.
