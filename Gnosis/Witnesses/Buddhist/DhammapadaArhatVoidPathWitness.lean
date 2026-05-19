import Gnosis.Witnesses.Buddhist.DhammacakkappavattanaWheelWitness

namespace Gnosis.Witnesses.Buddhist

/-!
# Dhammapada Arhat Void Path Witness

Witness ledger for `docs/ebooks/source-texts/dhammapada-muller.txt`,
chapter 7, "The Venerable (Arhat)".

The Arhat pattern is a trace-thinning witness: finished journey, grief abandoned,
void and unconditioned freedom perceived, senses subdued, quiet thought/word/deed,
and no new births in store.
-/

structure FinishedJourney where
  noSufferingAfterJourneyFinished : Bool := true
  griefAbandoned : Bool := true
  freedOnAllSides : Bool := true
  fettersThrownOff : Bool := true
  thoughtsWellCollected : Bool := true
  leavesHomeLikeSwanLake : Bool := true
deriving Repr, DecidableEq

structure VoidUnconditionedPath where
  noRichesRecognisedFood : Bool := true
  voidFreedomPerceived : Bool := true
  unconditionedFreedomPerceived : Bool := true
  pathDifficultLikeBirdsInAir : Bool := true
  appetitesStilled : Bool := true
  notAbsorbedInEnjoyment : Bool := true
deriving Repr, DecidableEq

structure QuietArhatClassifier where
  sensesSubduedLikeHorses : Bool := true
  prideFree : Bool := true
  lakeWithoutMud : Bool := true
  noNewBirths : Bool := true
  quietThoughtWordDeed : Bool := true
  uncreatedKnown : Bool := true
  allTiesCut : Bool := true
  passionlessFindForestDelight : Bool := true
deriving Repr, DecidableEq

def finishedJourney : FinishedJourney := {}
def voidUnconditionedPath : VoidUnconditionedPath := {}
def quietArhatClassifier : QuietArhatClassifier := {}

theorem dhammapada_finished_journey :
    finishedJourney.noSufferingAfterJourneyFinished = true ∧
      finishedJourney.griefAbandoned = true ∧
      finishedJourney.freedOnAllSides = true ∧
      finishedJourney.fettersThrownOff = true ∧
      finishedJourney.thoughtsWellCollected = true ∧
      finishedJourney.leavesHomeLikeSwanLake = true := by
  simp [finishedJourney]

theorem dhammapada_void_unconditioned_path :
    voidUnconditionedPath.noRichesRecognisedFood = true ∧
      voidUnconditionedPath.voidFreedomPerceived = true ∧
      voidUnconditionedPath.unconditionedFreedomPerceived = true ∧
      voidUnconditionedPath.pathDifficultLikeBirdsInAir = true ∧
      voidUnconditionedPath.appetitesStilled = true ∧
      voidUnconditionedPath.notAbsorbedInEnjoyment = true := by
  simp [voidUnconditionedPath]

theorem dhammapada_quiet_arhat_classifier :
    quietArhatClassifier.sensesSubduedLikeHorses = true ∧
      quietArhatClassifier.prideFree = true ∧
      quietArhatClassifier.lakeWithoutMud = true ∧
      quietArhatClassifier.noNewBirths = true ∧
      quietArhatClassifier.quietThoughtWordDeed = true ∧
      quietArhatClassifier.uncreatedKnown = true ∧
      quietArhatClassifier.allTiesCut = true ∧
      quietArhatClassifier.passionlessFindForestDelight = true := by
  simp [quietArhatClassifier]

theorem dhammapada_arhat_void_path_witness :
    finishedJourney.noSufferingAfterJourneyFinished = true ∧
      finishedJourney.fettersThrownOff = true ∧
      voidUnconditionedPath.voidFreedomPerceived = true ∧
      voidUnconditionedPath.unconditionedFreedomPerceived = true ∧
      quietArhatClassifier.noNewBirths = true ∧
      quietArhatClassifier.quietThoughtWordDeed = true ∧
      quietArhatClassifier.uncreatedKnown = true := by
  simp [finishedJourney, voidUnconditionedPath, quietArhatClassifier]

end Gnosis.Witnesses.Buddhist
