import Gnosis.BuddhistAttachmentSkyrms

namespace Gnosis.Witnesses.Buddhist

/-!
# Dhammapada Fool Delayed Fruit Witness

Witness ledger for `docs/ebooks/source-texts/dhammapada-muller.txt`,
chapter 5, "The Fool".

The fool chapter is a delayed-fruit counterproof. False ownership torments the
agent, evil ripens after a latency interval, ascetic form does not equal wisdom,
and reputation/precedence desire pulls away from Nirvana.
-/

structure FoolOwnershipGap where
  lifeLongWithoutLaw : Bool := true
  noCompanionshipWithFool : Bool := true
  sonsWealthMineTorments : Bool := true
  selfNotOwnedBySelf : Bool := true
  foolKnowingFoolishnessPartlyWise : Bool := true
  foolThinkingWiseFoolIndeed : Bool := true
deriving Repr, DecidableEq

structure DelayedEvilFruit where
  foolGreatestEnemyToSelf : Bool := true
  deedRepentedNotWellDone : Bool := true
  deedUnrepentedWellDone : Bool := true
  evilInitiallyHoney : Bool := true
  evilRipensAsGrief : Bool := true
  evilMilkDoesNotTurnSuddenly : Bool := true
  evilFireCoveredByAshesFollows : Bool := true
deriving Repr, DecidableEq

structure ReputationNirvanaSplit where
  asceticFoodWithoutLawWorthLittle : Bool := true
  falseReputationDesiredByFool : Bool := true
  precedenceLordshipIncreasePride : Bool := true
  wealthRoadDiffersFromNirvanaRoad : Bool := true
  honourNotYearnedFor : Bool := true
  separationFromWorldStrivenFor : Bool := true
deriving Repr, DecidableEq

def foolOwnershipGap : FoolOwnershipGap := {}
def delayedEvilFruit : DelayedEvilFruit := {}
def reputationNirvanaSplit : ReputationNirvanaSplit := {}

theorem dhammapada_fool_ownership_gap :
    foolOwnershipGap.lifeLongWithoutLaw = true ∧
      foolOwnershipGap.noCompanionshipWithFool = true ∧
      foolOwnershipGap.sonsWealthMineTorments = true ∧
      foolOwnershipGap.selfNotOwnedBySelf = true ∧
      foolOwnershipGap.foolKnowingFoolishnessPartlyWise = true ∧
      foolOwnershipGap.foolThinkingWiseFoolIndeed = true := by
  simp [foolOwnershipGap]

theorem dhammapada_delayed_evil_fruit :
    delayedEvilFruit.foolGreatestEnemyToSelf = true ∧
      delayedEvilFruit.deedRepentedNotWellDone = true ∧
      delayedEvilFruit.deedUnrepentedWellDone = true ∧
      delayedEvilFruit.evilInitiallyHoney = true ∧
      delayedEvilFruit.evilRipensAsGrief = true ∧
      delayedEvilFruit.evilMilkDoesNotTurnSuddenly = true ∧
      delayedEvilFruit.evilFireCoveredByAshesFollows = true := by
  simp [delayedEvilFruit]

theorem dhammapada_reputation_nirvana_split :
    reputationNirvanaSplit.asceticFoodWithoutLawWorthLittle = true ∧
      reputationNirvanaSplit.falseReputationDesiredByFool = true ∧
      reputationNirvanaSplit.precedenceLordshipIncreasePride = true ∧
      reputationNirvanaSplit.wealthRoadDiffersFromNirvanaRoad = true ∧
      reputationNirvanaSplit.honourNotYearnedFor = true ∧
      reputationNirvanaSplit.separationFromWorldStrivenFor = true := by
  simp [reputationNirvanaSplit]

theorem dhammapada_fool_delayed_fruit_witness :
    foolOwnershipGap.sonsWealthMineTorments = true ∧
      foolOwnershipGap.selfNotOwnedBySelf = true ∧
      delayedEvilFruit.evilInitiallyHoney = true ∧
      delayedEvilFruit.evilRipensAsGrief = true ∧
      reputationNirvanaSplit.wealthRoadDiffersFromNirvanaRoad = true ∧
      reputationNirvanaSplit.falseReputationDesiredByFool = true := by
  simp [foolOwnershipGap, delayedEvilFruit, reputationNirvanaSplit]

end Gnosis.Witnesses.Buddhist
