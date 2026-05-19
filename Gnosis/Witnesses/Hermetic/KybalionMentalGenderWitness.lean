import Gnosis.Witnesses.Hermetic.KybalionGenderCreationWitness

namespace Gnosis.Witnesses.Hermetic

/-! Witness ledger for `kybalion-three-initiates.txt`, chapter 14. -/

structure MentalGender where
  dualMindAncientlyKnown : Bool := true
  iAndMeDistinguished : Bool := true
  meAsMentalWomb : Bool := true
  bodyClothesFeelingsNotSelf : Bool := true
  iAsWillWitness : Bool := true
  willProjectsEnergyToMe : Bool := true
  correspondenceWithCreation : Bool := true
  suggestionUsesVibrationGender : Bool := true
  cuckooEggImplantWarning : Bool := true
  inactiveWillRuledByOthers : Bool := true
  iMeCoordinationNeeded : Bool := true
deriving Repr, DecidableEq

def mentalGender : MentalGender := {}

theorem kybalion_mental_gender_witness :
    mentalGender.dualMindAncientlyKnown = true ∧
      mentalGender.iAndMeDistinguished = true ∧
      mentalGender.meAsMentalWomb = true ∧
      mentalGender.bodyClothesFeelingsNotSelf = true ∧
      mentalGender.iAsWillWitness = true ∧
      mentalGender.willProjectsEnergyToMe = true ∧
      mentalGender.correspondenceWithCreation = true ∧
      mentalGender.suggestionUsesVibrationGender = true ∧
      mentalGender.cuckooEggImplantWarning = true ∧
      mentalGender.inactiveWillRuledByOthers = true ∧
      mentalGender.iMeCoordinationNeeded = true := by
  simp [mentalGender]

end Gnosis.Witnesses.Hermetic
