import Gnosis.Recoverability

namespace Gnosis
namespace InformationAbsorption

open LayeredNoise

/-!
# Information Absorption

Absorption is observer-relative. A processor absorbs at most as many signal
units as its stable rows can hold; the remainder leaks as unresolved residue.
-/

def absorbedInfo (frame : ObserverFrame) (signal : HigherLayerSignal) : Nat :=
  signal.saturationWitness - unresolvedResidue frame signal

def leakedInfo (frame : ObserverFrame) (signal : HigherLayerSignal) : Nat :=
  unresolvedResidue frame signal

def perfectlyAligned (frame : ObserverFrame) (signal : HigherLayerSignal) : Prop :=
  signal.saturationWitness = frame.stableRows

theorem leakage_is_residue (frame : ObserverFrame) (signal : HigherLayerSignal) :
    leakedInfo frame signal = unresolvedResidue frame signal := by
  rfl

theorem absorption_plus_leakage
    (frame : ObserverFrame) (signal : HigherLayerSignal)
    (hRows : frame.stableRows ≤ signal.saturationWitness) :
    absorbedInfo frame signal + leakedInfo frame signal = signal.saturationWitness := by
  unfold absorbedInfo leakedInfo unresolvedResidue
  omega

theorem absorption_limit
    (frame : ObserverFrame) (signal : HigherLayerSignal)
    (hRows : frame.stableRows ≤ signal.saturationWitness) :
    absorbedInfo frame signal ≤ frame.stableRows := by
  unfold absorbedInfo unresolvedResidue
  omega

theorem under_saturation_absorbs_all
    (frame : ObserverFrame) (signal : HigherLayerSignal)
    (hUnder : signal.saturationWitness ≤ frame.stableRows) :
    unresolvedResidue frame signal = 0 := by
  exact Nat.sub_eq_zero_of_le hUnder

theorem perfect_alignment_zero_leak
    (frame : ObserverFrame) (signal : HigherLayerSignal)
    (hAlign : perfectlyAligned frame signal) :
    leakedInfo frame signal = 0 := by
  unfold leakedInfo unresolvedResidue perfectlyAligned at *
  rw [hAlign]
  exact Nat.sub_eq_zero_of_le (Nat.le_refl _)

theorem white_is_fully_absorbed_by_aeon :
    leakedInfo aeonObserver whiteSaturationSignal = 0 := by
  unfold leakedInfo unresolvedResidue aeonObserver whiteSaturationSignal
  decide

theorem pink_partial_absorption_at_aeon :
    absorbedInfo aeonObserver pinkSaturationSignal = Gnosis.Circadian.aeon := by
  unfold absorbedInfo
  rw [pink_overflows_aeon_by_eighteen]
  decide

theorem pink_leakage_at_aeon :
    leakedInfo aeonObserver pinkSaturationSignal = 18 := by
  exact pink_overflows_aeon_by_eighteen

theorem brown_leakage_at_aeon :
    leakedInfo aeonObserver brownSaturationSignal = 78 := by
  unfold leakedInfo unresolvedResidue aeonObserver brownSaturationSignal
  decide

def witness17Frame : ObserverFrame :=
  { bandwidth := 17, stableRows := 17 }

def witness22Frame : ObserverFrame :=
  { bandwidth := 22, stableRows := 22 }

theorem witness17_absorbs_more_than_aeon_on_pink :
    absorbedInfo aeonObserver pinkSaturationSignal <
      absorbedInfo witness17Frame pinkSaturationSignal := by
  unfold absorbedInfo unresolvedResidue aeonObserver witness17Frame pinkSaturationSignal
  decide

theorem witness22_absorbs_more_than_witness17_on_pink :
    absorbedInfo witness17Frame pinkSaturationSignal <
      absorbedInfo witness22Frame pinkSaturationSignal := by
  unfold absorbedInfo unresolvedResidue witness17Frame witness22Frame pinkSaturationSignal
  decide

theorem witness22_still_leaks_on_pink :
    leakedInfo witness22Frame pinkSaturationSignal = 8 := by
  unfold leakedInfo unresolvedResidue witness22Frame pinkSaturationSignal
  decide

end InformationAbsorption
end Gnosis
