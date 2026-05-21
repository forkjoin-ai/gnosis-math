import Gnosis.ScribalStandingWave.TranscriptAuditTrace

namespace Gnosis
namespace ScribalStandingWave

def taggedTranscriptModeRank (mode : TaggedTranscriptMode) : Nat :=
  match mode with
  | TaggedTranscriptMode.tagged => 0
  | TaggedTranscriptMode.rawEscape => 1

def boolRank (value : Bool) : Nat :=
  if value then 1 else 0

def transcriptAuditAtomRank (atom : TranscriptAuditAtom) : Nat :=
  atom.turnIndex * 1000000 +
  atom.contentHash * 100 +
  taggedTranscriptModeRank atom.mode * 16 +
  boolRank atom.auditTagPresent * 8 +
  boolRank atom.escapeGap * 4 +
  boolRank atom.claimsSourceAuthority

def transcriptAuditAtomLe
    (left right : TranscriptAuditAtom) : Bool :=
  transcriptAuditAtomRank left <= transcriptAuditAtomRank right

def insertTranscriptAuditAtom
    (atom : TranscriptAuditAtom) :
    List TranscriptAuditAtom → List TranscriptAuditAtom
  | [] => [atom]
  | head :: tail =>
      if transcriptAuditAtomLe atom head then
        atom :: head :: tail
      else
        head :: insertTranscriptAuditAtom atom tail

def sortTranscriptAuditAtoms :
    List TranscriptAuditAtom → List TranscriptAuditAtom
  | [] => []
  | head :: tail =>
      insertTranscriptAuditAtom head (sortTranscriptAuditAtoms tail)

def canonicalTranscriptAuditAtoms
    (atoms : List TranscriptAuditAtom) : List TranscriptAuditAtom :=
  sortTranscriptAuditAtoms (transcriptAuditJoin [] atoms)

def canonicalTranscriptAuditJoin
    (left right : List TranscriptAuditAtom) : List TranscriptAuditAtom :=
  canonicalTranscriptAuditAtoms (transcriptAuditJoin left right)

def transcriptAuditJoinEquivalent
    (left right : List TranscriptAuditAtom) : Bool :=
  canonicalTranscriptAuditAtoms left = canonicalTranscriptAuditAtoms right

def canonicalAtomA : TranscriptAuditAtom :=
  transcriptAuditAtomFromTurn canonicalTaggedTranscriptTurn

def canonicalAtomB : TranscriptAuditAtom :=
  transcriptAuditAtomFromTurn secondTaggedTranscriptTurn

def canonicalAtomGap : TranscriptAuditAtom :=
  transcriptAuditAtomFromTurn rawEscapeTranscriptTurn

theorem canonical_transcript_audit_join_idempotent :
    canonicalTranscriptAuditJoin [canonicalAtomA] [canonicalAtomA] =
      canonicalTranscriptAuditAtoms [canonicalAtomA] := by
  decide

theorem canonical_transcript_audit_join_commutative :
    transcriptAuditJoinEquivalent
      (canonicalTranscriptAuditJoin [canonicalAtomA] [canonicalAtomB])
      (canonicalTranscriptAuditJoin [canonicalAtomB] [canonicalAtomA]) =
        true := by
  decide

theorem canonical_transcript_audit_join_associative :
    transcriptAuditJoinEquivalent
      (canonicalTranscriptAuditJoin
        (canonicalTranscriptAuditJoin [canonicalAtomA] [canonicalAtomB])
        [canonicalAtomGap])
      (canonicalTranscriptAuditJoin
        [canonicalAtomA]
        (canonicalTranscriptAuditJoin [canonicalAtomB] [canonicalAtomGap])) =
        true := by
  decide

theorem canonical_transcript_audit_join_preserves_raw_gap :
    transcriptAuditAtomPresent canonicalAtomGap
      (canonicalTranscriptAuditJoin [canonicalAtomA] [canonicalAtomGap]) =
        true := by
  decide

end ScribalStandingWave
end Gnosis
