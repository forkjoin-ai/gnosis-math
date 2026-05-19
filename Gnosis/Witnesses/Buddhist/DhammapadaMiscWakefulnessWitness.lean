import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Buddhist

/-!
# Dhammapada Miscellaneous Wakefulness Witness

Witness ledger for `docs/ebooks/source-texts/dhammapada-muller.txt`,
chapter 21, "Miscellaneous".
-/

structure SmallGreatPleasureChoice where
  smallPleasureLeftForGreat : Bool := true
  pleasureByHurtingOthersBindsHatred : Bool := true
  neglectedDutyIncreasesDesire : Bool := true
  bodyWatchfulnessEndsDesire : Bool := true
deriving Repr, DecidableEq

structure SymbolicSeverance where
  parentKingKingdomKillingReadAsSeverance : Bool := true
  BrahmanaScathelessAfterSeverance : Bool := true
  literalHarmNotEndorsed : Bool := true
  sourceRequiresContextGuard : Bool := true
deriving Repr, DecidableEq

structure SixfoldWakefulness where
  awakeOnBuddha : Bool := true
  awakeOnLaw : Bool := true
  awakeOnChurch : Bool := true
  awakeOnBody : Bool := true
  awakeOnCompassion : Bool := true
  awakeOnMeditation : Bool := true
  alonePracticeDestroysDesires : Bool := true
  goodShineFromAfar : Bool := true
deriving Repr, DecidableEq

def smallGreatPleasureChoice : SmallGreatPleasureChoice := {}
def symbolicSeverance : SymbolicSeverance := {}
def sixfoldWakefulness : SixfoldWakefulness := {}

theorem dhammapada_small_great_pleasure_choice :
    smallGreatPleasureChoice.smallPleasureLeftForGreat = true ∧
      smallGreatPleasureChoice.pleasureByHurtingOthersBindsHatred = true ∧
      smallGreatPleasureChoice.neglectedDutyIncreasesDesire = true ∧
      smallGreatPleasureChoice.bodyWatchfulnessEndsDesire = true := by
  simp [smallGreatPleasureChoice]

theorem dhammapada_symbolic_severance :
    symbolicSeverance.parentKingKingdomKillingReadAsSeverance = true ∧
      symbolicSeverance.BrahmanaScathelessAfterSeverance = true ∧
      symbolicSeverance.literalHarmNotEndorsed = true ∧
      symbolicSeverance.sourceRequiresContextGuard = true := by
  simp [symbolicSeverance]

theorem dhammapada_sixfold_wakefulness :
    sixfoldWakefulness.awakeOnBuddha = true ∧
      sixfoldWakefulness.awakeOnLaw = true ∧
      sixfoldWakefulness.awakeOnChurch = true ∧
      sixfoldWakefulness.awakeOnBody = true ∧
      sixfoldWakefulness.awakeOnCompassion = true ∧
      sixfoldWakefulness.awakeOnMeditation = true ∧
      sixfoldWakefulness.alonePracticeDestroysDesires = true ∧
      sixfoldWakefulness.goodShineFromAfar = true := by
  simp [sixfoldWakefulness]

theorem dhammapada_misc_wakefulness_witness :
    smallGreatPleasureChoice.smallPleasureLeftForGreat = true ∧
      smallGreatPleasureChoice.bodyWatchfulnessEndsDesire = true ∧
      symbolicSeverance.literalHarmNotEndorsed = true ∧
      symbolicSeverance.sourceRequiresContextGuard = true ∧
      sixfoldWakefulness.awakeOnBuddha = true ∧
      sixfoldWakefulness.awakeOnCompassion = true ∧
      sixfoldWakefulness.alonePracticeDestroysDesires = true := by
  simp [smallGreatPleasureChoice, symbolicSeverance, sixfoldWakefulness]

end Gnosis.Witnesses.Buddhist
