import Gnosis.Witnesses.Buddhist.DhammacakkappavattanaWheelWitness

namespace Gnosis.Witnesses.Buddhist

/-!
# Dhammapada Old Age House-Builder Witness

Witness ledger for `docs/ebooks/source-texts/dhammapada-muller.txt`,
chapter 11, "Old Age".

The chapter makes decay unavoidable but not meaningless. Body and chariot break;
virtue remains. The strong witness is the house-builder passage: once the maker
is seen, rafters and ridge-pole are broken and desire is extinguished.
-/

structure BurningWorldBodyDecay where
  worldAlwaysBurning : Bool := true
  lightSoughtInDarkness : Bool := true
  dressedLumpWoundedSickly : Bool := true
  bodyFrailCorruptionBreaks : Bool := true
  whiteBonesLikeThrownGourds : Bool := true
  strongholdContainsOldAgeDeathPrideDeceit : Bool := true
deriving Repr, DecidableEq

structure VirtueOutlastsChariot where
  kingChariotsDestroyed : Bool := true
  bodyApproachesDestruction : Bool := true
  virtueDoesNotApproachDestruction : Bool := true
  fleshMayGrowWithoutKnowledge : Bool := true
deriving Repr, DecidableEq

structure HouseBuilderBroken where
  manyBirthsWhileBuilderUnfound : Bool := true
  birthAgainAgainPainful : Bool := true
  makerSeen : Bool := true
  tabernacleNotMadeAgain : Bool := true
  raftersBroken : Bool := true
  ridgePoleSundered : Bool := true
  mindApproachesEternal : Bool := true
  desiresExtinguished : Bool := true
  undisciplinedOldAgeWastes : Bool := true
deriving Repr, DecidableEq

def burningWorldBodyDecay : BurningWorldBodyDecay := {}
def virtueOutlastsChariot : VirtueOutlastsChariot := {}
def houseBuilderBroken : HouseBuilderBroken := {}

theorem dhammapada_burning_world_body_decay :
    burningWorldBodyDecay.worldAlwaysBurning = true ∧
      burningWorldBodyDecay.lightSoughtInDarkness = true ∧
      burningWorldBodyDecay.dressedLumpWoundedSickly = true ∧
      burningWorldBodyDecay.bodyFrailCorruptionBreaks = true ∧
      burningWorldBodyDecay.whiteBonesLikeThrownGourds = true ∧
      burningWorldBodyDecay.strongholdContainsOldAgeDeathPrideDeceit = true := by
  simp [burningWorldBodyDecay]

theorem dhammapada_virtue_outlasts_chariot :
    virtueOutlastsChariot.kingChariotsDestroyed = true ∧
      virtueOutlastsChariot.bodyApproachesDestruction = true ∧
      virtueOutlastsChariot.virtueDoesNotApproachDestruction = true ∧
      virtueOutlastsChariot.fleshMayGrowWithoutKnowledge = true := by
  simp [virtueOutlastsChariot]

theorem dhammapada_house_builder_broken :
    houseBuilderBroken.manyBirthsWhileBuilderUnfound = true ∧
      houseBuilderBroken.birthAgainAgainPainful = true ∧
      houseBuilderBroken.makerSeen = true ∧
      houseBuilderBroken.tabernacleNotMadeAgain = true ∧
      houseBuilderBroken.raftersBroken = true ∧
      houseBuilderBroken.ridgePoleSundered = true ∧
      houseBuilderBroken.mindApproachesEternal = true ∧
      houseBuilderBroken.desiresExtinguished = true ∧
      houseBuilderBroken.undisciplinedOldAgeWastes = true := by
  simp [houseBuilderBroken]

theorem dhammapada_old_age_house_builder_witness :
    burningWorldBodyDecay.worldAlwaysBurning = true ∧
      virtueOutlastsChariot.virtueDoesNotApproachDestruction = true ∧
      houseBuilderBroken.makerSeen = true ∧
      houseBuilderBroken.raftersBroken = true ∧
      houseBuilderBroken.ridgePoleSundered = true ∧
      houseBuilderBroken.desiresExtinguished = true := by
  simp [burningWorldBodyDecay, virtueOutlastsChariot, houseBuilderBroken]

end Gnosis.Witnesses.Buddhist
