import Gnosis.Witnesses.Hermetic.KybalionAllUnknowableWitness

namespace Gnosis.Witnesses.Hermetic

/-! Witness ledger for `kybalion-three-initiates.txt`, chapter 5. -/

structure MentalUniverse where
  universeHeldInMindOfAll : Bool := true
  spiritTermExceedsDefinition : Bool := true
  creationAnalogizedByMentalImage : Bool := true
  finiteImagesGiveCorrespondenceOnly : Bool := true
  universeRelativeYetPracticallyReal : Bool := true
  mentalPowerNaturalForce : Bool := true
  lawsUsedToRiseHigher : Bool := true
  denialAsHalfWisdomRejected : Bool := true
  transmutationNotPresumptuousDenial : Bool := true
deriving Repr, DecidableEq

def mentalUniverse : MentalUniverse := {}

theorem kybalion_mental_universe_witness :
    mentalUniverse.universeHeldInMindOfAll = true ∧
      mentalUniverse.spiritTermExceedsDefinition = true ∧
      mentalUniverse.creationAnalogizedByMentalImage = true ∧
      mentalUniverse.finiteImagesGiveCorrespondenceOnly = true ∧
      mentalUniverse.universeRelativeYetPracticallyReal = true ∧
      mentalUniverse.mentalPowerNaturalForce = true ∧
      mentalUniverse.lawsUsedToRiseHigher = true ∧
      mentalUniverse.denialAsHalfWisdomRejected = true ∧
      mentalUniverse.transmutationNotPresumptuousDenial = true := by
  simp [mentalUniverse]

end Gnosis.Witnesses.Hermetic
