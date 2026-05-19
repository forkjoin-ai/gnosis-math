import Gnosis.Witnesses.Hindu.GitaImperishableYogaWitness

namespace Gnosis.Witnesses.Hindu

/-! Witness ledger for `bhagavad-gita-arnold.txt`, chapter 5. -/

structure SankhyaYogaUnity where
  workInHolinessBetterThanRefraining : Bool := true
  trueRenouncerSeeksNoughtRejectsNought : Bool := true
  sankhyaYogaSeenAsOne : Bool := true
  pureSelfRuledLordOfSenses : Bool := true
  commonLifeOfAllLiving : Bool := true
  deedTaintDoesNotTouch : Bool := true
deriving Repr, DecidableEq

structure LotusAction where
  senseWorldPlaysWithSenses : Bool := true
  actDetachedFromEnd : Bool := true
  lotusLeafUnstained : Bool := true
  fruitRenouncedGainsPeace : Bool := true
  fruitSeekingFastenedDown : Bool := true
  nineGateCityNonDoership : Bool := true
  selfPushesWorkPassionFruit : Bool := true
deriving Repr, DecidableEq

structure UnityVision where
  knowledgeSunChasesDarkness : Bool := true
  noReturnRoad : Bool := true
  equalBrahmanCowElephantDogOutcast : Bool := true
  worldOvercomeByUnityFaith : Bool := true
  joyGriefNotOverheld : Bool := true
  senseJoysBreedGriefs : Bool := true
  lustAngerMastered : Bool := true
  breathSenseConstrainedDeliverance : Bool := true
deriving Repr, DecidableEq

def sankhyaYogaUnity : SankhyaYogaUnity := {}
def lotusAction : LotusAction := {}
def unityVision : UnityVision := {}

theorem gita_sankhya_yoga_unity :
    sankhyaYogaUnity.workInHolinessBetterThanRefraining = true ∧
      sankhyaYogaUnity.trueRenouncerSeeksNoughtRejectsNought = true ∧
      sankhyaYogaUnity.sankhyaYogaSeenAsOne = true ∧
      sankhyaYogaUnity.pureSelfRuledLordOfSenses = true ∧
      sankhyaYogaUnity.commonLifeOfAllLiving = true ∧
      sankhyaYogaUnity.deedTaintDoesNotTouch = true := by
  simp [sankhyaYogaUnity]

theorem gita_lotus_action :
    lotusAction.senseWorldPlaysWithSenses = true ∧
      lotusAction.actDetachedFromEnd = true ∧
      lotusAction.lotusLeafUnstained = true ∧
      lotusAction.fruitRenouncedGainsPeace = true ∧
      lotusAction.fruitSeekingFastenedDown = true ∧
      lotusAction.nineGateCityNonDoership = true ∧
      lotusAction.selfPushesWorkPassionFruit = true := by
  simp [lotusAction]

theorem gita_unity_vision :
    unityVision.knowledgeSunChasesDarkness = true ∧
      unityVision.noReturnRoad = true ∧
      unityVision.equalBrahmanCowElephantDogOutcast = true ∧
      unityVision.worldOvercomeByUnityFaith = true ∧
      unityVision.joyGriefNotOverheld = true ∧
      unityVision.senseJoysBreedGriefs = true ∧
      unityVision.lustAngerMastered = true ∧
      unityVision.breathSenseConstrainedDeliverance = true := by
  simp [unityVision]

theorem gita_renouncing_fruit_witness :
    sankhyaYogaUnity.sankhyaYogaSeenAsOne = true ∧
      lotusAction.lotusLeafUnstained = true ∧
      lotusAction.nineGateCityNonDoership = true ∧
      unityVision.equalBrahmanCowElephantDogOutcast = true ∧
      unityVision.senseJoysBreedGriefs = true ∧
      unityVision.lustAngerMastered = true := by
  simp [sankhyaYogaUnity, lotusAction, unityVision]

end Gnosis.Witnesses.Hindu
