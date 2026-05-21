import Init

namespace Gnosis.Witnesses.Bible.Ephesians
namespace EphesiansDeadGraceWorkmanshipWitness

/-!
# Ephesians 2:1-10 -- Dead in Sins, Saved by Grace, Created for Good Works

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94050-94075`.

The passage moves from death-walk to mercy-quickening and then to workmanship.
Works are denied as salvation ground but restored as ordained walk after grace.

No `sorry`, no new `axiom`.
-/

structure FormerDeathWalk where
  deadInTrespassesAndSins : Bool := true
  walkedAccordingToWorldCourse : Bool := true
  princeOfPowerOfAirNamed : Bool := true
  childrenOfDisobedienceSpirit : Bool := true
  lustsOfFleshAndMind : Bool := true
  childrenOfWrathByNature : Bool := true
deriving DecidableEq, Repr

def formerDeathWalk : FormerDeathWalk := {}

def deathWalkWitness (d : FormerDeathWalk) : Prop :=
  d.deadInTrespassesAndSins = true ∧
  d.walkedAccordingToWorldCourse = true ∧
  d.princeOfPowerOfAirNamed = true ∧
  d.childrenOfDisobedienceSpirit = true ∧
  d.lustsOfFleshAndMind = true ∧
  d.childrenOfWrathByNature = true

structure GraceQuickeningWorkmanship where
  richMercyAndGreatLove : Bool := true
  quickenedTogetherWithChrist : Bool := true
  raisedAndSeatedTogether : Bool := true
  graceRichesShownInAges : Bool := true
  savedByGraceThroughFaith : Bool := true
  giftNotOfWorks : Bool := true
  workmanshipCreatedForGoodWorks : Bool := true
  goodWorksOrdainedToWalk : Bool := true
deriving DecidableEq, Repr

def graceQuickeningWorkmanship : GraceQuickeningWorkmanship := {}

def graceWorkmanshipWitness (g : GraceQuickeningWorkmanship) : Prop :=
  g.richMercyAndGreatLove = true ∧
  g.quickenedTogetherWithChrist = true ∧
  g.raisedAndSeatedTogether = true ∧
  g.graceRichesShownInAges = true ∧
  g.savedByGraceThroughFaith = true ∧
  g.giftNotOfWorks = true ∧
  g.workmanshipCreatedForGoodWorks = true ∧
  g.goodWorksOrdainedToWalk = true

theorem ephesians_death_walk :
    deathWalkWitness formerDeathWalk := by
  unfold deathWalkWitness formerDeathWalk
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ephesians_grace_workmanship :
    graceWorkmanshipWitness graceQuickeningWorkmanship := by
  unfold graceWorkmanshipWitness graceQuickeningWorkmanship
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ephesians_dead_grace_workmanship_witness :
    deathWalkWitness formerDeathWalk ∧
    graceWorkmanshipWitness graceQuickeningWorkmanship := by
  exact ⟨ephesians_death_walk,
    ephesians_grace_workmanship⟩

end EphesiansDeadGraceWorkmanshipWitness
end Gnosis.Witnesses.Bible.Ephesians
