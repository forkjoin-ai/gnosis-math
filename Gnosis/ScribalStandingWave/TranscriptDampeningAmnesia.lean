import Gnosis.ScribalStandingWave.TranscriptCrdtLaws

namespace Gnosis
namespace ScribalStandingWave

structure TranscriptRecallPolicy where
  currentTurnIndex : Nat
  activeWindow : Nat
  dampenedWeight : Nat
  amnesiaWeight : Nat
  deriving DecidableEq, Repr

structure TranscriptRecallAtom where
  atom : TranscriptAuditAtom
  active : Bool
  dampened : Bool
  amnesiaGap : Bool
  recallWeight : Nat
  claimsSourceAuthority : Bool
  deriving DecidableEq, Repr

def transcriptAtomAge
    (policy : TranscriptRecallPolicy)
    (atom : TranscriptAuditAtom) : Nat :=
  policy.currentTurnIndex - atom.turnIndex

def transcriptAtomActive
    (policy : TranscriptRecallPolicy)
    (atom : TranscriptAuditAtom) : Bool :=
  transcriptAtomAge policy atom <= policy.activeWindow

def transcriptRecallAtomFromAudit
    (policy : TranscriptRecallPolicy)
    (atom : TranscriptAuditAtom) : TranscriptRecallAtom :=
  let active := transcriptAtomActive policy atom
  let amnesiaGap := atom.mode = TaggedTranscriptMode.rawEscape
  { atom := atom
    active := active
    dampened := !active && !amnesiaGap
    amnesiaGap := amnesiaGap
    recallWeight :=
      if amnesiaGap then policy.amnesiaWeight
      else if active then 100
      else policy.dampenedWeight
    claimsSourceAuthority := atom.claimsSourceAuthority }

def transcriptRecallAtomSound (recall : TranscriptRecallAtom) : Bool :=
  transcriptAuditAtomSound recall.atom &&
  !recall.claimsSourceAuthority &&
  (if recall.amnesiaGap then recall.recallWeight = 0 else true)

def transcriptRecallView
    (policy : TranscriptRecallPolicy)
    (atoms : List TranscriptAuditAtom) : List TranscriptRecallAtom :=
  atoms.map (transcriptRecallAtomFromAudit policy)

def transcriptRecallViewSound (recalls : List TranscriptRecallAtom) : Bool :=
  recalls.all transcriptRecallAtomSound

def canonicalRecallPolicy : TranscriptRecallPolicy where
  currentTurnIndex := 10
  activeWindow := 2
  dampenedWeight := 25
  amnesiaWeight := 0

def activeRecallPolicy : TranscriptRecallPolicy where
  currentTurnIndex := 1
  activeWindow := 2
  dampenedWeight := 25
  amnesiaWeight := 0

def canonicalRecallView : List TranscriptRecallAtom :=
  transcriptRecallView canonicalRecallPolicy
    [canonicalAtomA, canonicalAtomB, canonicalAtomGap]

def activeRecallView : List TranscriptRecallAtom :=
  transcriptRecallView activeRecallPolicy [canonicalAtomA, canonicalAtomB]

theorem canonical_recall_view_sound :
    transcriptRecallViewSound canonicalRecallView = true := by
  decide

theorem active_recall_view_keeps_recent_atoms_full_weight :
    (transcriptRecallView activeRecallPolicy [canonicalAtomB]).all
      (fun recall => recall.active && recall.recallWeight = 100) = true := by
  decide

theorem old_tagged_recall_is_dampened_not_deleted :
    (transcriptRecallView canonicalRecallPolicy [canonicalAtomA]).all
      (fun recall => recall.dampened && recall.recallWeight = 25) = true := by
  decide

theorem raw_escape_recall_becomes_amnesia_gap :
    (transcriptRecallView canonicalRecallPolicy [canonicalAtomGap]).all
      (fun recall => recall.amnesiaGap && recall.recallWeight = 0) = true := by
  decide

end ScribalStandingWave
end Gnosis
