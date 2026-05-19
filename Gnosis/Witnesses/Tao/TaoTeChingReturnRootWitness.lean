import Gnosis.GnosisTriptychBraid

namespace Gnosis.Witnesses.Tao
namespace TaoTeChingReturnRootWitness

/-!
# Tao Te Ching -- Return to Root and Artificial Virtue

Source text: `docs/ebooks/source-texts/tao-te-ching-legge.txt`;
text anchor `docs/ebooks/source-texts/tao-te-ching-legge.txt:250-369`.

No `sorry`, no new `axiom`.
-/

structure StillnessClears where
  muddyWaterClearsByStillness : Bool
  restArisesThroughContinuedMovement : Bool
  notFullOfSelf : Bool
  vacancyUtmost : Bool
  stillnessGuarded : Bool
  returnToRoot : Bool
deriving DecidableEq, Repr

def taoStillnessClears : StillnessClears where
  muddyWaterClearsByStillness := true
  restArisesThroughContinuedMovement := true
  notFullOfSelf := true
  vacancyUtmost := true
  stillnessGuarded := true
  returnToRoot := true

def rootReturnStillness (s : StillnessClears) : Prop :=
  s.muddyWaterClearsByStillness = true ∧
  s.restArisesThroughContinuedMovement = true ∧
  s.notFullOfSelf = true ∧
  s.vacancyUtmost = true ∧
  s.stillnessGuarded = true ∧
  s.returnToRoot = true

structure LostTaoSymptoms where
  bestRulersBarelyKnown : Bool
  workDonePeopleSaySelfSo : Bool
  taoLostVirtueAppears : Bool
  wisdomAppearsHypocrisyEnsues : Bool
  disorderManufacturesLoyalty : Bool
  contrivanceProducesTheft : Bool
deriving DecidableEq, Repr

def taoLostTaoSymptoms : LostTaoSymptoms where
  bestRulersBarelyKnown := true
  workDonePeopleSaySelfSo := true
  taoLostVirtueAppears := true
  wisdomAppearsHypocrisyEnsues := true
  disorderManufacturesLoyalty := true
  contrivanceProducesTheft := true

def artificialVirtueIsGap (g : LostTaoSymptoms) : Prop :=
  g.bestRulersBarelyKnown = true ∧
  g.workDonePeopleSaySelfSo = true ∧
  g.taoLostVirtueAppears = true ∧
  g.wisdomAppearsHypocrisyEnsues = true ∧
  g.disorderManufacturesLoyalty = true ∧
  g.contrivanceProducesTheft = true

structure MotherSourcePreference where
  renounceLearningTroublesCease : Bool
  crowdSatisfiedButSageDrifts : Bool
  brightnessNotTrusted : Bool
  discriminationNotTrusted : Bool
  valuesNursingMother : Bool
deriving DecidableEq, Repr

def taoMotherSourcePreference : MotherSourcePreference where
  renounceLearningTroublesCease := true
  crowdSatisfiedButSageDrifts := true
  brightnessNotTrusted := true
  discriminationNotTrusted := true
  valuesNursingMother := true

def motherSourceBeatsPublicBrightness (m : MotherSourcePreference) : Prop :=
  m.renounceLearningTroublesCease = true ∧
  m.crowdSatisfiedButSageDrifts = true ∧
  m.brightnessNotTrusted = true ∧
  m.discriminationNotTrusted = true ∧
  m.valuesNursingMother = true

theorem tao_root_return_stillness :
    rootReturnStillness taoStillnessClears := by
  unfold rootReturnStillness taoStillnessClears
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tao_artificial_virtue_gap :
    artificialVirtueIsGap taoLostTaoSymptoms := by
  unfold artificialVirtueIsGap taoLostTaoSymptoms
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tao_mother_source_preference :
    motherSourceBeatsPublicBrightness taoMotherSourcePreference := by
  unfold motherSourceBeatsPublicBrightness taoMotherSourcePreference
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem tao_return_recovery_shape :
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom :=
  Gnosis.GnosisTriptychBraid.two_step_recovery

theorem tao_te_ching_return_root_witness :
    rootReturnStillness taoStillnessClears ∧
    artificialVirtueIsGap taoLostTaoSymptoms ∧
    motherSourceBeatsPublicBrightness taoMotherSourcePreference ∧
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom := by
  exact ⟨tao_root_return_stillness,
    tao_artificial_virtue_gap,
    tao_mother_source_preference,
    tao_return_recovery_shape⟩

end TaoTeChingReturnRootWitness
end Gnosis.Witnesses.Tao
