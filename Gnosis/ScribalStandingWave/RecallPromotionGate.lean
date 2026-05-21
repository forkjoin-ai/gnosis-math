import Gnosis.ScribalStandingWave.TranscriptDampeningAmnesia

namespace Gnosis
namespace ScribalStandingWave

structure RecallPromotionEvidence where
  corroboratingAtom : TranscriptAuditAtom
  fresh : Bool
  deriving DecidableEq, Repr

def sameRecallContent
    (left right : TranscriptAuditAtom) : Bool :=
  left.contentHash = right.contentHash

def recallPromotionEvidenceSound
    (recall : TranscriptRecallAtom)
    (evidence : RecallPromotionEvidence) : Bool :=
  recall.dampened &&
  !recall.amnesiaGap &&
  evidence.fresh &&
  evidence.corroboratingAtom.mode = TaggedTranscriptMode.tagged &&
  evidence.corroboratingAtom.auditTagPresent &&
  !evidence.corroboratingAtom.claimsSourceAuthority &&
  sameRecallContent recall.atom evidence.corroboratingAtom

def promoteRecallAtom
    (recall : TranscriptRecallAtom)
    (evidence : RecallPromotionEvidence) : TranscriptRecallAtom :=
  if recallPromotionEvidenceSound recall evidence then
    { recall with active := true, dampened := false, recallWeight := 100 }
  else
    recall

def promotedRecallAtomSound
    (recall : TranscriptRecallAtom)
    (evidence : RecallPromotionEvidence) : Bool :=
  transcriptRecallAtomSound (promoteRecallAtom recall evidence)

def staleRecallAtom : TranscriptRecallAtom :=
  transcriptRecallAtomFromAudit canonicalRecallPolicy canonicalAtomA

def freshCorroboratingAtom : TranscriptAuditAtom :=
  { canonicalAtomA with turnIndex := 11 }

def freshCorroboratingEvidence : RecallPromotionEvidence where
  corroboratingAtom := freshCorroboratingAtom
  fresh := true

def staleCorroboratingEvidence : RecallPromotionEvidence :=
  { freshCorroboratingEvidence with fresh := false }

def rawGapPromotionEvidence : RecallPromotionEvidence where
  corroboratingAtom := canonicalAtomGap
  fresh := true

theorem fresh_tagged_evidence_promotes_dampened_recall :
    (promoteRecallAtom staleRecallAtom freshCorroboratingEvidence).active =
      true := by
  decide

theorem fresh_tagged_evidence_restores_full_weight :
    (promoteRecallAtom staleRecallAtom freshCorroboratingEvidence).recallWeight =
      100 := by
  decide

theorem stale_evidence_does_not_promote_recall :
    promoteRecallAtom staleRecallAtom staleCorroboratingEvidence =
      staleRecallAtom := by
  decide

theorem raw_gap_evidence_does_not_promote_recall :
    promoteRecallAtom staleRecallAtom rawGapPromotionEvidence =
      staleRecallAtom := by
  decide

theorem promoted_recall_atom_remains_sound :
    promotedRecallAtomSound staleRecallAtom freshCorroboratingEvidence =
      true := by
  decide

end ScribalStandingWave
end Gnosis
