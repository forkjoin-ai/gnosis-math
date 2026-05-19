import Gnosis.GnosisTriptychBraid

namespace Gnosis.Witnesses.Hindu

/-! Witness ledger for `bhagavad-gita-arnold.txt`, chapter 2. -/

structure ImperishableLife where
  wiseMournNeitherLivingNorDead : Bool := true
  spiritNeverWasNot : Bool := true
  framesPerish : Bool := true
  lifeCannotSlayOrBeSlain : Bool := true
  wornRobesChangedForNew : Bool := true
  weaponsCannotReachLife : Bool := true
  birthDeathCycleOrdained : Bool := true
deriving Repr, DecidableEq

structure NonFruitAction where
  pairsHeldAlike : Bool := true
  littleFaithSavesFromDread : Bool := true
  freeFromThreeQualities : Bool := true
  rightDeedMotiveNotFruit : Bool := true
  actionWithoutSelfGain : Bool := true
  equabilityIsYoga : Bool := true
  meditationGivesPeace : Bool := true
deriving Repr, DecidableEq

structure SteadyWisdom where
  desiresAbandoned : Bool := true
  sorrowJoyEquanimity : Bool := true
  tortoiseSenseWithdrawal : Bool := true
  desireChainUndoesMind : Bool := true
  governedWillSetsSoulAtPeace : Bool := true
  oceanReceivesWithoutOverflow : Bool := true
  selfSinAbandonedTouchesTranquility : Bool := true
deriving Repr, DecidableEq

def imperishableLife : ImperishableLife := {}
def nonFruitAction : NonFruitAction := {}
def steadyWisdom : SteadyWisdom := {}

theorem gita_imperishable_life :
    imperishableLife.wiseMournNeitherLivingNorDead = true ∧
      imperishableLife.spiritNeverWasNot = true ∧
      imperishableLife.framesPerish = true ∧
      imperishableLife.lifeCannotSlayOrBeSlain = true ∧
      imperishableLife.weaponsCannotReachLife = true ∧
      imperishableLife.birthDeathCycleOrdained = true := by
  simp [imperishableLife]

theorem gita_non_fruit_action :
    nonFruitAction.pairsHeldAlike = true ∧
      nonFruitAction.littleFaithSavesFromDread = true ∧
      nonFruitAction.freeFromThreeQualities = true ∧
      nonFruitAction.rightDeedMotiveNotFruit = true ∧
      nonFruitAction.actionWithoutSelfGain = true ∧
      nonFruitAction.equabilityIsYoga = true ∧
      nonFruitAction.meditationGivesPeace = true := by
  simp [nonFruitAction]

theorem gita_steady_wisdom :
    steadyWisdom.desiresAbandoned = true ∧
      steadyWisdom.sorrowJoyEquanimity = true ∧
      steadyWisdom.tortoiseSenseWithdrawal = true ∧
      steadyWisdom.desireChainUndoesMind = true ∧
      steadyWisdom.governedWillSetsSoulAtPeace = true ∧
      steadyWisdom.oceanReceivesWithoutOverflow = true ∧
      steadyWisdom.selfSinAbandonedTouchesTranquility = true := by
  simp [steadyWisdom]

theorem gita_imperishable_yoga_witness :
    imperishableLife.lifeCannotSlayOrBeSlain = true ∧
      nonFruitAction.rightDeedMotiveNotFruit = true ∧
      nonFruitAction.equabilityIsYoga = true ∧
      steadyWisdom.tortoiseSenseWithdrawal = true ∧
      steadyWisdom.desireChainUndoesMind = true ∧
      steadyWisdom.oceanReceivesWithoutOverflow = true := by
  simp [imperishableLife, nonFruitAction, steadyWisdom]

end Gnosis.Witnesses.Hindu
