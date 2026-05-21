namespace Gnosis.Witnesses.Bible.SecondJohn
namespace SecondJohnTruthLoveHospitalityWitness

/-!
# 2 John -- Truth-Love, Flesh-Coming, and Hospitality Boundary Control

Source slice: 2 John 1:1-13.

Book invariant: truth is not an opinion held by an individual; it dwells in the
community and remains with it. Love is not soft permission; love is walking
after commandments heard from the beginning.

Primary gap/counterproof: hospitality is participation. The strange severity of
"receive him not into your house" is not rudeness but boundary logic: to bless a
doctrine that denies Christ come in flesh is to share in the evil works carried
by that doctrine.

Unseen sat: 2 John turns 1 John's idol firewall into household protocol. Truth
and love must travel together, or both decay: truth without love becomes sterile
exclusion, while love without doctrine becomes an open port for antichrist.

No `sorry`, no new `axiom`.
-/

structure TruthDwellingGreeting where
  elderLovesInTruth : Bool := true
  allTruthKnowersShareLove : Bool := true
  truthDwellsInUs : Bool := true
  truthWithUsForever : Bool := true
  graceMercyPeaceInTruthAndLove : Bool := true
deriving DecidableEq, Repr

def truthDwellingGreeting : TruthDwellingGreeting := {}

def truthDwellingLedger (t : TruthDwellingGreeting) : Prop :=
  t.elderLovesInTruth = true ∧
  t.allTruthKnowersShareLove = true ∧
  t.truthDwellsInUs = true ∧
  t.truthWithUsForever = true ∧
  t.graceMercyPeaceInTruthAndLove = true

structure CommandLoveWalk where
  childrenFoundWalkingInTruth : Bool := true
  commandReceivedFromFather : Bool := true
  noNewCommandButBeginningLove : Bool := true
  loveWalksAfterCommandments : Bool := true
  beginningCommandMustBeWalked : Bool := true
deriving DecidableEq, Repr

def commandLoveWalk : CommandLoveWalk := {}

def loveIsCommandWalk (c : CommandLoveWalk) : Prop :=
  c.childrenFoundWalkingInTruth = true ∧
  c.commandReceivedFromFather = true ∧
  c.noNewCommandButBeginningLove = true ∧
  c.loveWalksAfterCommandments = true ∧
  c.beginningCommandMustBeWalked = true

structure HospitalityBoundary where
  manyDeceiversEnteredWorld : Bool := true
  fleshComingDenialMarksAntichrist : Bool := true
  selfWatchPreservesFullReward : Bool := true
  doctrineAbidingHoldsFatherAndSon : Bool := true
  falseDoctrineNotReceivedIntoHouse : Bool := true
  blessingFalseTeacherSharesWorks : Bool := true
  faceToFaceCompletesJoyBeyondInk : Bool := true
deriving DecidableEq, Repr

def hospitalityBoundary : HospitalityBoundary := {}

def participationBoundaryWitness (h : HospitalityBoundary) : Prop :=
  h.manyDeceiversEnteredWorld = true ∧
  h.fleshComingDenialMarksAntichrist = true ∧
  h.selfWatchPreservesFullReward = true ∧
  h.doctrineAbidingHoldsFatherAndSon = true ∧
  h.falseDoctrineNotReceivedIntoHouse = true ∧
  h.blessingFalseTeacherSharesWorks = true ∧
  h.faceToFaceCompletesJoyBeyondInk = true

theorem second_john_truth_dwelling :
    truthDwellingLedger truthDwellingGreeting := by
  unfold truthDwellingLedger truthDwellingGreeting
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem second_john_love_command_walk :
    loveIsCommandWalk commandLoveWalk := by
  unfold loveIsCommandWalk commandLoveWalk
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem second_john_participation_boundary :
    participationBoundaryWitness hospitalityBoundary := by
  unfold participationBoundaryWitness hospitalityBoundary
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem second_john_truth_love_hospitality_witness :
    truthDwellingLedger truthDwellingGreeting ∧
    loveIsCommandWalk commandLoveWalk ∧
    participationBoundaryWitness hospitalityBoundary := by
  exact ⟨second_john_truth_dwelling,
    second_john_love_command_walk,
    second_john_participation_boundary⟩

end SecondJohnTruthLoveHospitalityWitness
end Gnosis.Witnesses.Bible.SecondJohn
