import Gnosis.Mesh.MeshStateVibration

namespace Gnosis.Witnesses.Hermetic

/-! Witness ledger for `kybalion-three-initiates.txt`, chapter 9. -/

structure VibrationScale where
  nothingRests : Bool := true
  differencesAreRatesOfVibration : Bool := true
  spiritAndMatterAreScalePoles : Bool := true
  highVibrationSeemsStill : Bool := true
  lowVibrationSeemsStill : Bool := true
  mentalStatesHaveRates : Bool := true
  vibrationChangeChangesMentalState : Bool := true
  masteryChangesOwnVibrations : Bool := true
  inductionAffectsOthersGuardedBySelfKnowledge : Bool := true
deriving Repr, DecidableEq

def vibrationScale : VibrationScale := {}

theorem kybalion_vibration_scale_witness :
    vibrationScale.nothingRests = true ∧
      vibrationScale.differencesAreRatesOfVibration = true ∧
      vibrationScale.spiritAndMatterAreScalePoles = true ∧
      vibrationScale.highVibrationSeemsStill = true ∧
      vibrationScale.mentalStatesHaveRates = true ∧
      vibrationScale.vibrationChangeChangesMentalState = true ∧
      vibrationScale.masteryChangesOwnVibrations = true ∧
      vibrationScale.inductionAffectsOthersGuardedBySelfKnowledge = true := by
  simp [vibrationScale]

end Gnosis.Witnesses.Hermetic
