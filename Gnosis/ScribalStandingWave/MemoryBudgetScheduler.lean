import Gnosis.ScribalStandingWave.RecallPromotionGate

namespace Gnosis
namespace ScribalStandingWave

structure MemoryBudgetPolicy where
  activeBudget : Nat
  deriving DecidableEq, Repr

structure ScheduledMemoryAtom where
  recall : TranscriptRecallAtom
  promoted : Bool
  priority : Nat
  deriving DecidableEq, Repr

structure ScheduledTranscriptMemory where
  activeMemory : List ScheduledMemoryAtom
  auditGaps : List TranscriptRecallAtom
  activeBudget : Nat
  deriving DecidableEq, Repr

def recallHasPromotionEvidence
    (recall : TranscriptRecallAtom)
    (evidence : List RecallPromotionEvidence) : Bool :=
  evidence.any (fun candidate =>
    recallPromotionEvidenceSound recall candidate)

def scheduledMemoryAtomFromRecall
    (evidence : List RecallPromotionEvidence)
    (recall : TranscriptRecallAtom) : ScheduledMemoryAtom :=
  let promoted := recallHasPromotionEvidence recall evidence
  let promotedRecall :=
    if promoted then
      match evidence.find? (fun candidate =>
        recallPromotionEvidenceSound recall candidate) with
      | some candidate => promoteRecallAtom recall candidate
      | none => recall
    else
      recall
  { recall := promotedRecall
    promoted := promoted
    priority :=
      if promoted then 3
      else if recall.active then 2
      else if recall.dampened then 1
      else 0 }

def scheduledAtomLe
    (left right : ScheduledMemoryAtom) : Bool :=
  right.priority <= left.priority

def insertScheduledMemoryAtom
    (atom : ScheduledMemoryAtom) :
    List ScheduledMemoryAtom → List ScheduledMemoryAtom
  | [] => [atom]
  | head :: tail =>
      if scheduledAtomLe atom head then
        atom :: head :: tail
      else
        head :: insertScheduledMemoryAtom atom tail

def sortScheduledMemoryAtoms :
    List ScheduledMemoryAtom → List ScheduledMemoryAtom
  | [] => []
  | head :: tail =>
      insertScheduledMemoryAtom head (sortScheduledMemoryAtoms tail)

def scheduleTranscriptMemory
    (policy : MemoryBudgetPolicy)
    (recalls : List TranscriptRecallAtom)
    (evidence : List RecallPromotionEvidence) : ScheduledTranscriptMemory :=
  let activeCandidates :=
    recalls.filter (fun recall => !recall.amnesiaGap)
  let gaps :=
    recalls.filter (fun recall => recall.amnesiaGap)
  { activeMemory :=
      (sortScheduledMemoryAtoms
        (activeCandidates.map (scheduledMemoryAtomFromRecall evidence))).take
          policy.activeBudget
    auditGaps := gaps
    activeBudget := policy.activeBudget }

def scheduledTranscriptMemorySound
    (schedule : ScheduledTranscriptMemory) : Bool :=
  schedule.activeMemory.length <= schedule.activeBudget &&
  schedule.activeMemory.all (fun atom =>
    transcriptRecallAtomSound atom.recall &&
    !atom.recall.amnesiaGap &&
    !atom.recall.claimsSourceAuthority) &&
  schedule.auditGaps.all (fun gap =>
    gap.amnesiaGap && !gap.claimsSourceAuthority)

def canonicalMemoryBudgetPolicy : MemoryBudgetPolicy where
  activeBudget := 2

def canonicalSchedulableRecalls : List TranscriptRecallAtom :=
  transcriptRecallView canonicalRecallPolicy
    [canonicalAtomA, canonicalAtomB, canonicalAtomGap]

def canonicalScheduledTranscriptMemory : ScheduledTranscriptMemory :=
  scheduleTranscriptMemory canonicalMemoryBudgetPolicy
    canonicalSchedulableRecalls [freshCorroboratingEvidence]

def authorityRecallAtom : TranscriptRecallAtom :=
  { staleRecallAtom with claimsSourceAuthority := true }

def authorityScheduledTranscriptMemory : ScheduledTranscriptMemory :=
  scheduleTranscriptMemory canonicalMemoryBudgetPolicy
    [authorityRecallAtom] [freshCorroboratingEvidence]

theorem canonical_schedule_under_budget_sound :
    scheduledTranscriptMemorySound canonicalScheduledTranscriptMemory =
      true := by
  decide

theorem canonical_schedule_respects_finite_budget :
    canonicalScheduledTranscriptMemory.activeMemory.length <=
      canonicalScheduledTranscriptMemory.activeBudget := by
  decide

theorem authority_schedule_unsound :
    scheduledTranscriptMemorySound authorityScheduledTranscriptMemory =
      false := by
  decide

theorem promoted_atom_outranks_recent_active_atom :
    (scheduleTranscriptMemory canonicalMemoryBudgetPolicy
      [staleRecallAtom,
        transcriptRecallAtomFromAudit activeRecallPolicy canonicalAtomB]
      [freshCorroboratingEvidence]).activeMemory.head?.map
        (fun atom => atom.promoted) = some true := by
  decide

theorem dampened_atom_available_when_budget_permits :
    (scheduleTranscriptMemory { activeBudget := 3 }
      [staleRecallAtom] []).activeMemory.length = 1 := by
  decide

theorem amnesia_gap_preserved_outside_active_memory :
    canonicalScheduledTranscriptMemory.auditGaps.length = 1 ∧
    canonicalScheduledTranscriptMemory.activeMemory.all
      (fun atom => !atom.recall.amnesiaGap) = true := by
  decide

end ScribalStandingWave
end Gnosis
