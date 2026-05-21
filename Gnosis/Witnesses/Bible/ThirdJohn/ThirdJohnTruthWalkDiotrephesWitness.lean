namespace Gnosis.Witnesses.Bible.ThirdJohn
namespace ThirdJohnTruthWalkDiotrephesWitness

/-!
# 3 John -- Truth-Walk, Fellowhelpers, and Diotrephes as Gate Capture

Source slice: 3 John 1:1-14.

Book invariant: truth has testimony-bearing movement. Gaius is not praised for
owning a private correct opinion; brethren testify that truth is in him because
he walks in truth and materially forwards those who went out for the Name.

Primary gap/counterproof: preeminence-love corrupts reception. Diotrephes does
not merely disagree; he refuses apostolic reception, prates with malicious
words, blocks brethren, forbids receivers, and casts them out. This is namespace
capture: a local gatekeeper preferring rank over truth flow.

Unseen sat: Demetrius supplies the positive multi-source record. Good report of
all, the truth itself, and apostolic record converge. 3 John is a small epistle
because its theorem is small and sharp: receive truth-bearers, reject
preeminence capture, and let face-to-face fellowship complete what ink cannot.

No `sorry`, no new `axiom`.
-/

structure GaiusTruthWalk where
  lovedInTruth : Bool := true
  soulProsperingNamed : Bool := true
  brethrenTestifyTruthInHim : Bool := true
  walksInTruth : Bool := true
  noGreaterJoyThanChildrenTruthWalk : Bool := true
deriving DecidableEq, Repr

def gaiusTruthWalk : GaiusTruthWalk := {}

def truthWalkTestimony (g : GaiusTruthWalk) : Prop :=
  g.lovedInTruth = true ∧
  g.soulProsperingNamed = true ∧
  g.brethrenTestifyTruthInHim = true ∧
  g.walksInTruth = true ∧
  g.noGreaterJoyThanChildrenTruthWalk = true

structure FellowhelperHospitality where
  faithfulWorkTowardBrethrenAndStrangers : Bool := true
  charityBorneWitnessBeforeChurch : Bool := true
  godlyForwardingCommended : Bool := true
  workersTakeNothingFromGentiles : Bool := true
  receivingMakesFellowhelpersToTruth : Bool := true
deriving DecidableEq, Repr

def fellowhelperHospitality : FellowhelperHospitality := {}

def supportBecomesTruthLabor (f : FellowhelperHospitality) : Prop :=
  f.faithfulWorkTowardBrethrenAndStrangers = true ∧
  f.charityBorneWitnessBeforeChurch = true ∧
  f.godlyForwardingCommended = true ∧
  f.workersTakeNothingFromGentiles = true ∧
  f.receivingMakesFellowhelpersToTruth = true

structure DiotrephesDemetriusBoundary where
  preeminenceLoveRejectsReception : Bool := true
  maliciousWordsPrated : Bool := true
  brethrenReceptionBlocked : Bool := true
  receiversForbiddenAndCastOut : Bool := true
  goodDoingMarksGodwardSight : Bool := true
  demetriusHasThreefoldWitness : Bool := true
  faceToFacePreferredBeyondInk : Bool := true
deriving DecidableEq, Repr

def diotrephesDemetriusBoundary : DiotrephesDemetriusBoundary := {}

def preeminenceCaptureRejected (d : DiotrephesDemetriusBoundary) : Prop :=
  d.preeminenceLoveRejectsReception = true ∧
  d.maliciousWordsPrated = true ∧
  d.brethrenReceptionBlocked = true ∧
  d.receiversForbiddenAndCastOut = true ∧
  d.goodDoingMarksGodwardSight = true ∧
  d.demetriusHasThreefoldWitness = true ∧
  d.faceToFacePreferredBeyondInk = true

theorem third_john_truth_walk :
    truthWalkTestimony gaiusTruthWalk := by
  unfold truthWalkTestimony gaiusTruthWalk
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem third_john_support_truth_labor :
    supportBecomesTruthLabor fellowhelperHospitality := by
  unfold supportBecomesTruthLabor fellowhelperHospitality
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem third_john_preeminence_capture_rejected :
    preeminenceCaptureRejected diotrephesDemetriusBoundary := by
  unfold preeminenceCaptureRejected diotrephesDemetriusBoundary
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem third_john_truth_walk_diotrephes_witness :
    truthWalkTestimony gaiusTruthWalk ∧
    supportBecomesTruthLabor fellowhelperHospitality ∧
    preeminenceCaptureRejected diotrephesDemetriusBoundary := by
  exact ⟨third_john_truth_walk,
    third_john_support_truth_labor,
    third_john_preeminence_capture_rejected⟩

end ThirdJohnTruthWalkDiotrephesWitness
end Gnosis.Witnesses.Bible.ThirdJohn
