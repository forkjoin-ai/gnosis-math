import Init

namespace Gnosis.Witnesses.Bible.Colossians
namespace ColossiansCompleteInChristWitness

/-!
# Colossians 2:1-15 -- Complete in Christ, Not Spoiled by Vain Deceit

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94734-94780`.

The anti-spoilage protocol is direct: all treasures are in Christ, so philosophy,
vain deceit, traditions, and rudiments cannot complete what is already complete
in him.

No `sorry`, no new `axiom`.
-/

structure KnitMysteryTreasures where
  conflictForColosseLaodicea : Bool := true
  heartsComfortedKnitLove : Bool := true
  fullAssuranceUnderstanding : Bool := true
  mysteryOfGodChristAcknowledged : Bool := true
  treasuresWisdomKnowledgeHidden : Bool := true
  enticingWordsBeguileRejected : Bool := true
  orderAndSteadfastFaithJoyed : Bool := true
deriving DecidableEq, Repr

def knitMysteryTreasures : KnitMysteryTreasures := {}

def mysteryTreasureWitness (m : KnitMysteryTreasures) : Prop :=
  m.conflictForColosseLaodicea = true ∧ m.heartsComfortedKnitLove = true ∧
  m.fullAssuranceUnderstanding = true ∧ m.mysteryOfGodChristAcknowledged = true ∧
  m.treasuresWisdomKnowledgeHidden = true ∧ m.enticingWordsBeguileRejected = true ∧
  m.orderAndSteadfastFaithJoyed = true

structure CompleteInChrist where
  receivedChristWalkInHim : Bool := true
  rootedBuiltEstablishedThankful : Bool := true
  spoilageByPhilosophyRejected : Bool := true
  fullnessGodheadBodily : Bool := true
  completeInHeadOfPowers : Bool := true
  circumcisionWithoutHands : Bool := true
  buriedRisenThroughFaith : Bool := true
  deadQuickenedForgiven : Bool := true
  handwritingNailedToCross : Bool := true
  powersSpoiledOpenlyTriumphed : Bool := true
deriving DecidableEq, Repr

def completeInChrist : CompleteInChrist := {}

def completeInChristWitness (c : CompleteInChrist) : Prop :=
  c.receivedChristWalkInHim = true ∧ c.rootedBuiltEstablishedThankful = true ∧
  c.spoilageByPhilosophyRejected = true ∧ c.fullnessGodheadBodily = true ∧
  c.completeInHeadOfPowers = true ∧ c.circumcisionWithoutHands = true ∧
  c.buriedRisenThroughFaith = true ∧ c.deadQuickenedForgiven = true ∧
  c.handwritingNailedToCross = true ∧ c.powersSpoiledOpenlyTriumphed = true

theorem colossians_mystery_treasure :
    mysteryTreasureWitness knitMysteryTreasures := by
  unfold mysteryTreasureWitness knitMysteryTreasures
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem colossians_complete_in_christ :
    completeInChristWitness completeInChrist := by
  unfold completeInChristWitness completeInChrist
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem colossians_complete_in_christ_witness :
    mysteryTreasureWitness knitMysteryTreasures ∧
    completeInChristWitness completeInChrist := by
  exact ⟨colossians_mystery_treasure, colossians_complete_in_christ⟩

end ColossiansCompleteInChristWitness
end Gnosis.Witnesses.Bible.Colossians
