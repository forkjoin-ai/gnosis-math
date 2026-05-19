import Gnosis.GnosisTriptychBraid

namespace Gnosis.Witnesses.Tao
namespace TaoTeChingBellowsWaterWitness

/-!
# Tao Te Ching -- Bellows, Valley, Water, and Last Place

Source text: `docs/ebooks/source-texts/tao-te-ching-legge.txt`;
text anchor `docs/ebooks/source-texts/tao-te-ching-legge.txt:105-181`.

No `sorry`, no new `axiom`.
-/

structure EmptyPower where
  heavenEarthNotSentimental : Bool
  bellowsEmptiedNotExhausted : Bool
  muchSpeechExhausts : Bool
  valleySpiritDoesNotDie : Bool
  usedGentlyWithoutPain : Bool
deriving DecidableEq, Repr

def taoEmptyPower : EmptyPower where
  heavenEarthNotSentimental := true
  bellowsEmptiedNotExhausted := true
  muchSpeechExhausts := true
  valleySpiritDoesNotDie := true
  usedGentlyWithoutPain := true

def emptinessCarriesPower (p : EmptyPower) : Prop :=
  p.heavenEarthNotSentimental = true ∧
  p.bellowsEmptiedNotExhausted = true ∧
  p.muchSpeechExhausts = true ∧
  p.valleySpiritDoesNotDie = true ∧
  p.usedGentlyWithoutPain = true

structure WaterLastPlace where
  doesNotLiveForSelf : Bool
  selfLastBecomesForemost : Bool
  noPrivateEndsRealizesEnds : Bool
  waterBenefitsAll : Bool
  waterOccupiesLowPlace : Bool
  doesNotWrangle : Bool
deriving DecidableEq, Repr

def taoWaterLastPlace : WaterLastPlace where
  doesNotLiveForSelf := true
  selfLastBecomesForemost := true
  noPrivateEndsRealizesEnds := true
  waterBenefitsAll := true
  waterOccupiesLowPlace := true
  doesNotWrangle := true

def lowPlaceWinsWithoutStriving (w : WaterLastPlace) : Prop :=
  w.doesNotLiveForSelf = true ∧
  w.selfLastBecomesForemost = true ∧
  w.noPrivateEndsRealizesEnds = true ∧
  w.waterBenefitsAll = true ∧
  w.waterOccupiesLowPlace = true ∧
  w.doesNotWrangle = true

structure FullnessWarning where
  vesselBestUnfilled : Bool
  sharpPointCannotLast : Bool
  goldJadeUnsafe : Bool
  arroganceBringsEvil : Bool
  withdrawAfterWork : Bool
  producesWithoutClaim : Bool
deriving DecidableEq, Repr

def taoFullnessWarning : FullnessWarning where
  vesselBestUnfilled := true
  sharpPointCannotLast := true
  goldJadeUnsafe := true
  arroganceBringsEvil := true
  withdrawAfterWork := true
  producesWithoutClaim := true

def fullnessIsFailureMode (f : FullnessWarning) : Prop :=
  f.vesselBestUnfilled = true ∧
  f.sharpPointCannotLast = true ∧
  f.goldJadeUnsafe = true ∧
  f.arroganceBringsEvil = true ∧
  f.withdrawAfterWork = true ∧
  f.producesWithoutClaim = true

theorem tao_emptiness_power :
    emptinessCarriesPower taoEmptyPower := by
  unfold emptinessCarriesPower taoEmptyPower
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem tao_low_place_wins :
    lowPlaceWinsWithoutStriving taoWaterLastPlace := by
  unfold lowPlaceWinsWithoutStriving taoWaterLastPlace
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tao_fullness_failure :
    fullnessIsFailureMode taoFullnessWarning := by
  unfold fullnessIsFailureMode taoFullnessWarning
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tao_bellows_recovery_shape :
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom :=
  Gnosis.GnosisTriptychBraid.two_step_recovery

theorem tao_te_ching_bellows_water_witness :
    emptinessCarriesPower taoEmptyPower ∧
    lowPlaceWinsWithoutStriving taoWaterLastPlace ∧
    fullnessIsFailureMode taoFullnessWarning ∧
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom := by
  exact ⟨tao_emptiness_power,
    tao_low_place_wins,
    tao_fullness_failure,
    tao_bellows_recovery_shape⟩

end TaoTeChingBellowsWaterWitness
end Gnosis.Witnesses.Tao
