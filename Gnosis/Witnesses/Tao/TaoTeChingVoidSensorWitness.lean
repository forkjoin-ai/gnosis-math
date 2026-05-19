import Gnosis.LaoziBowlVoidFunctionWitness
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Tao
namespace TaoTeChingVoidSensorWitness

/-!
# Tao Te Ching -- Productive Void and Anti-Sensory One

Source text: `docs/ebooks/source-texts/tao-te-ching-legge.txt`;
text anchor `docs/ebooks/source-texts/tao-te-ching-legge.txt:184-247`.

No `sorry`, no new `axiom`.
-/

inductive SensorName where
  | equable
  | inaudible
  | subtle
deriving DecidableEq, Repr, Nonempty

inductive SensorTruth where
  | oneBeyondDescription
deriving DecidableEq, Repr

def sensorNamesAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : SensorName => SensorTruth.oneBeyondDescription)
      SensorTruth.oneBeyondDescription :=
  TruthOneManyNamesWitness.constant_names_agree SensorTruth.oneBeyondDescription

structure ProductiveVoid where
  wheelUseDependsOnNaveVoid : Bool
  vesselUseDependsOnHollow : Bool
  roomUseDependsOnOpenSpace : Bool
  positiveExistenceAdapts : Bool
  nonhavingCarriesUse : Bool
deriving DecidableEq, Repr

def taoProductiveVoid : ProductiveVoid where
  wheelUseDependsOnNaveVoid := true
  vesselUseDependsOnHollow := true
  roomUseDependsOnOpenSpace := true
  positiveExistenceAdapts := true
  nonhavingCarriesUse := true

def voidIsUseSite (v : ProductiveVoid) : Prop :=
  v.wheelUseDependsOnNaveVoid = true ∧
  v.vesselUseDependsOnHollow = true ∧
  v.roomUseDependsOnOpenSpace = true ∧
  v.positiveExistenceAdapts = true ∧
  v.nonhavingCarriesUse = true

structure SensorFailure where
  lookDoNotSee : Bool
  listenDoNotHear : Bool
  graspDoNotHold : Bool
  threeCannotDescribe : Bool
  blendIntoOne : Bool
  formOfFormless : Bool
deriving DecidableEq, Repr

def taoSensorFailure : SensorFailure where
  lookDoNotSee := true
  listenDoNotHear := true
  graspDoNotHold := true
  threeCannotDescribe := true
  blendIntoOne := true
  formOfFormless := true

def sensorsFailIntoOne (s : SensorFailure) : Prop :=
  s.lookDoNotSee = true ∧
  s.listenDoNotHear = true ∧
  s.graspDoNotHold = true ∧
  s.threeCannotDescribe = true ∧
  s.blendIntoOne = true ∧
  s.formOfFormless = true

theorem tao_void_use_site :
    voidIsUseSite taoProductiveVoid := by
  unfold voidIsUseSite taoProductiveVoid
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem tao_sensor_failure_one :
    sensorsFailIntoOne taoSensorFailure := by
  unfold sensorsFailIntoOne taoSensorFailure
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tao_inherits_laozi_bowl (clay voidFunctional : Prop)
    (hc : clay) (hv : voidFunctional) :
    clay ∧ voidFunctional :=
  LaoziBowlVoidFunctionWitness.shell_and_void_together clay voidFunctional
    (LaoziBowlVoidFunctionWitness.buildWitness clay voidFunctional hc hv)

theorem tao_te_ching_void_sensor_witness :
    voidIsUseSite taoProductiveVoid ∧
    sensorsFailIntoOne taoSensorFailure ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : SensorName => SensorTruth.oneBeyondDescription)
      SensorTruth.oneBeyondDescription := by
  exact ⟨tao_void_use_site,
    tao_sensor_failure_one,
    sensorNamesAgree⟩

end TaoTeChingVoidSensorWitness
end Gnosis.Witnesses.Tao
