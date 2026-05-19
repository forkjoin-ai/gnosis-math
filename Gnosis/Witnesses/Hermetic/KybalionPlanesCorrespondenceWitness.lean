import Gnosis.Witnesses.Hermetic.KybalionSevenPrinciplesWitness

namespace Gnosis.Witnesses.Hermetic

/-! Witness ledger for `kybalion-three-initiates.txt`, chapter 8. -/

structure PlanesCorrespondence where
  aboveBelowCorrespond : Bool := true
  planesAreVibrationDegrees : Bool := true
  physicalMentalSpiritualPlanes : Bool := true
  divisionsArtificialAndShading : Bool := true
  matterAsLowVibrationEnergy : Bool := true
  lifeMindScaleContinuous : Bool := true
  spiritualPlanesExceedDescription : Bool := true
  highBeingsStillBelowAbsoluteSpirit : Bool := true
  dangerousKnowledgeGuarded : Bool := true
deriving Repr, DecidableEq

def planesCorrespondence : PlanesCorrespondence := {}

theorem kybalion_planes_correspondence_witness :
    planesCorrespondence.aboveBelowCorrespond = true ∧
      planesCorrespondence.planesAreVibrationDegrees = true ∧
      planesCorrespondence.physicalMentalSpiritualPlanes = true ∧
      planesCorrespondence.divisionsArtificialAndShading = true ∧
      planesCorrespondence.matterAsLowVibrationEnergy = true ∧
      planesCorrespondence.lifeMindScaleContinuous = true ∧
      planesCorrespondence.highBeingsStillBelowAbsoluteSpirit = true ∧
      planesCorrespondence.dangerousKnowledgeGuarded = true := by
  simp [planesCorrespondence]

end Gnosis.Witnesses.Hermetic
