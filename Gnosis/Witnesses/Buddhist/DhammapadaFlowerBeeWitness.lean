import Gnosis.GnosisTriptychBraid

namespace Gnosis.Witnesses.Buddhist

/-!
# Dhammapada Flower Bee Witness

Witness ledger for `docs/ebooks/source-texts/dhammapada-muller.txt`,
chapter 4, "Flowers".

The flower chapter distinguishes extraction from injury. Fine words without
action are scentless flowers; virtue travels against the wind.
-/

structure DistractedFlowerCapture where
  discipleFindsPathLikeFlower : Bool := true
  bodyFrothMirageKnown : Bool := true
  maraFlowerArrowBroken : Bool := true
  distractedGathererFloodedByDeath : Bool := true
  pleasureUnsatiatedBeforeDeath : Bool := true
deriving Repr, DecidableEq

structure BeeNonInjuryPractice where
  beeTakesNectarWithoutInjury : Bool := true
  sageAttendsOwnMisdeeds : Bool := true
  fineWordsWithoutActionScentless : Bool := true
  fineWordsWithActionFruitful : Bool := true
  manyGoodThingsFromMortalBirth : Bool := true
deriving Repr, DecidableEq

structure VirtueAgainstWind where
  flowerScentCannotTravelAgainstWind : Bool := true
  goodPeopleScentTravelsAgainstWind : Bool := true
  virtuePerfumeUnsurpassed : Bool := true
  trueKnowledgeHidesPathFromMara : Bool := true
  lilyGrowsFromRubbishHeap : Bool := true
  discipleShinesAmongDarkWalkers : Bool := true
deriving Repr, DecidableEq

def distractedFlowerCapture : DistractedFlowerCapture := {}
def beeNonInjuryPractice : BeeNonInjuryPractice := {}
def virtueAgainstWind : VirtueAgainstWind := {}

theorem dhammapada_distracted_flower_capture :
    distractedFlowerCapture.discipleFindsPathLikeFlower = true ∧
      distractedFlowerCapture.bodyFrothMirageKnown = true ∧
      distractedFlowerCapture.maraFlowerArrowBroken = true ∧
      distractedFlowerCapture.distractedGathererFloodedByDeath = true ∧
      distractedFlowerCapture.pleasureUnsatiatedBeforeDeath = true := by
  simp [distractedFlowerCapture]

theorem dhammapada_bee_non_injury_practice :
    beeNonInjuryPractice.beeTakesNectarWithoutInjury = true ∧
      beeNonInjuryPractice.sageAttendsOwnMisdeeds = true ∧
      beeNonInjuryPractice.fineWordsWithoutActionScentless = true ∧
      beeNonInjuryPractice.fineWordsWithActionFruitful = true ∧
      beeNonInjuryPractice.manyGoodThingsFromMortalBirth = true := by
  simp [beeNonInjuryPractice]

theorem dhammapada_virtue_against_wind :
    virtueAgainstWind.flowerScentCannotTravelAgainstWind = true ∧
      virtueAgainstWind.goodPeopleScentTravelsAgainstWind = true ∧
      virtueAgainstWind.virtuePerfumeUnsurpassed = true ∧
      virtueAgainstWind.trueKnowledgeHidesPathFromMara = true ∧
      virtueAgainstWind.lilyGrowsFromRubbishHeap = true ∧
      virtueAgainstWind.discipleShinesAmongDarkWalkers = true := by
  simp [virtueAgainstWind]

theorem dhammapada_flower_bee_witness :
    distractedFlowerCapture.bodyFrothMirageKnown = true ∧
      beeNonInjuryPractice.beeTakesNectarWithoutInjury = true ∧
      beeNonInjuryPractice.fineWordsWithoutActionScentless = true ∧
      beeNonInjuryPractice.fineWordsWithActionFruitful = true ∧
      virtueAgainstWind.goodPeopleScentTravelsAgainstWind = true ∧
      virtueAgainstWind.trueKnowledgeHidesPathFromMara = true := by
  simp [distractedFlowerCapture, beeNonInjuryPractice, virtueAgainstWind]

end Gnosis.Witnesses.Buddhist
