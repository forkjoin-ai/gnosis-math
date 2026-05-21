import Init

namespace Gnosis.Witnesses.Bible.Galatians
namespace GalatiansPillarsFellowshipWitness

/-!
# Galatians 2:6-10 -- Pillars, Person-Respect, and Fellowship

Source text: `docs/ebooks/source-texts/bible-kjv.txt:93648-93661`.

Institutional reputation does not add source authority. God accepts no man's
person, yet the pillars perceive grace and give fellowship while preserving the
Gentile/circumcision mission distinction and remembering the poor.

No `sorry`, no new `axiom`.
-/

structure ReputationNoAddition where
  seemedSomewhatNamed : Bool := true
  godAcceptsNoMansPerson : Bool := true
  conferenceAddedNothing : Bool := true
deriving DecidableEq, Repr

def reputationNoAddition : ReputationNoAddition := {}

def reputationCannotAddSourceAuthority (r : ReputationNoAddition) : Prop :=
  r.seemedSomewhatNamed = true ∧
  r.godAcceptsNoMansPerson = true ∧
  r.conferenceAddedNothing = true

structure MissionFellowship where
  uncircumcisionGospelCommittedToPaul : Bool := true
  circumcisionGospelCommittedToPeter : Bool := true
  sameGodWorksInBothMissions : Bool := true
  jamesCephasJohnPillars : Bool := true
  graceGivenPerceived : Bool := true
  rightHandsOfFellowshipGiven : Bool := true
  poorRemembered : Bool := true
deriving DecidableEq, Repr

def missionFellowship : MissionFellowship := {}

def fellowshipRecognizesGraceWithoutCapture (m : MissionFellowship) : Prop :=
  m.uncircumcisionGospelCommittedToPaul = true ∧
  m.circumcisionGospelCommittedToPeter = true ∧
  m.sameGodWorksInBothMissions = true ∧
  m.jamesCephasJohnPillars = true ∧
  m.graceGivenPerceived = true ∧
  m.rightHandsOfFellowshipGiven = true ∧
  m.poorRemembered = true

theorem galatians_reputation_no_addition :
    reputationCannotAddSourceAuthority reputationNoAddition := by
  unfold reputationCannotAddSourceAuthority reputationNoAddition
  exact ⟨rfl, rfl, rfl⟩

theorem galatians_mission_fellowship :
    fellowshipRecognizesGraceWithoutCapture missionFellowship := by
  unfold fellowshipRecognizesGraceWithoutCapture missionFellowship
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem galatians_pillars_fellowship_witness :
    reputationCannotAddSourceAuthority reputationNoAddition ∧
    fellowshipRecognizesGraceWithoutCapture missionFellowship := by
  exact ⟨galatians_reputation_no_addition, galatians_mission_fellowship⟩

end GalatiansPillarsFellowshipWitness
end Gnosis.Witnesses.Bible.Galatians
