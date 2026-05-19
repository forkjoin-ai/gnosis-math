import Gnosis.Witnesses.Buddhist.DhammacakkappavattanaWheelWitness

namespace Gnosis.Witnesses.Buddhist

/-!
# Dhammapada Way Three Roads Witness

Witness ledger for `docs/ebooks/source-texts/dhammapada-muller.txt`,
chapter 20, "The Way".
-/

structure BestWayTruths where
  eightfoldBestWay : Bool := true
  fourWordsBestTruths : Bool := true
  passionlessnessBestVirtue : Bool := true
  eyesToSeeBestPerson : Bool := true
  noOtherPurifiesIntelligence : Bool := true
  maraDeceitElsewhere : Bool := true
  wayEndsPain : Bool := true
  selfEffortRequired : Bool := true
deriving Repr, DecidableEq

structure ImpermanencePurity where
  createdThingsPerish : Bool := true
  createdThingsGriefPain : Bool := true
  formsUnreal : Bool := true
  seeingMakesPassiveInPain : Bool := true
  purityWay : Bool := true
  slothMissesKnowledgeWay : Bool := true
deriving Repr, DecidableEq

structure ThreeRoadsForestCut where
  speechWatched : Bool := true
  mindRestrained : Bool := true
  bodyNoWrong : Bool := true
  threeRoadsClearAchieveWay : Bool := true
  zealGainsKnowledge : Bool := true
  lackZealLosesKnowledge : Bool := true
  forestOfLustCutDown : Bool := true
  selfLoveCutLikeLotus : Bool := true
  deathFloodDistractedHouseholder : Bool := true
  nirvanaWayQuicklyCleared : Bool := true
deriving Repr, DecidableEq

def bestWayTruths : BestWayTruths := {}
def impermanencePurity : ImpermanencePurity := {}
def threeRoadsForestCut : ThreeRoadsForestCut := {}

theorem dhammapada_best_way_truths :
    bestWayTruths.eightfoldBestWay = true ∧
      bestWayTruths.fourWordsBestTruths = true ∧
      bestWayTruths.passionlessnessBestVirtue = true ∧
      bestWayTruths.eyesToSeeBestPerson = true ∧
      bestWayTruths.noOtherPurifiesIntelligence = true ∧
      bestWayTruths.maraDeceitElsewhere = true ∧
      bestWayTruths.wayEndsPain = true ∧
      bestWayTruths.selfEffortRequired = true := by
  simp [bestWayTruths]

theorem dhammapada_impermanence_purity :
    impermanencePurity.createdThingsPerish = true ∧
      impermanencePurity.createdThingsGriefPain = true ∧
      impermanencePurity.formsUnreal = true ∧
      impermanencePurity.seeingMakesPassiveInPain = true ∧
      impermanencePurity.purityWay = true ∧
      impermanencePurity.slothMissesKnowledgeWay = true := by
  simp [impermanencePurity]

theorem dhammapada_three_roads_forest_cut :
    threeRoadsForestCut.speechWatched = true ∧
      threeRoadsForestCut.mindRestrained = true ∧
      threeRoadsForestCut.bodyNoWrong = true ∧
      threeRoadsForestCut.threeRoadsClearAchieveWay = true ∧
      threeRoadsForestCut.zealGainsKnowledge = true ∧
      threeRoadsForestCut.lackZealLosesKnowledge = true ∧
      threeRoadsForestCut.forestOfLustCutDown = true ∧
      threeRoadsForestCut.selfLoveCutLikeLotus = true ∧
      threeRoadsForestCut.deathFloodDistractedHouseholder = true ∧
      threeRoadsForestCut.nirvanaWayQuicklyCleared = true := by
  simp [threeRoadsForestCut]

theorem dhammapada_way_three_roads_witness :
    bestWayTruths.eightfoldBestWay = true ∧
      bestWayTruths.selfEffortRequired = true ∧
      impermanencePurity.createdThingsPerish = true ∧
      impermanencePurity.formsUnreal = true ∧
      threeRoadsForestCut.threeRoadsClearAchieveWay = true ∧
      threeRoadsForestCut.forestOfLustCutDown = true ∧
      threeRoadsForestCut.nirvanaWayQuicklyCleared = true := by
  simp [bestWayTruths, impermanencePurity, threeRoadsForestCut]

end Gnosis.Witnesses.Buddhist
