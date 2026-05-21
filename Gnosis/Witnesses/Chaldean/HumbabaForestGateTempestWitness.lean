import Gnosis.Witnesses.Chaldean.SevenWindsContainmentDeepWitness

namespace Gnosis.Witnesses.Chaldean
namespace HumbabaForestGateTempestWitness

/-!
# Humbaba Forest-Gate Tempest Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Chapters XIII
and XIV, Izdubar/Heabani expedition against Humbaba.

The Humbaba material is fragmentary, but it preserves a strong boundary pattern:
an unknown expedition, a forest of pine and cedar enclosed by barrier and gate,
the seat of gods and sanctuary of angels, Humbaba waiting in the forest path,
and a defender who pours a tempest from his mouth. The later summary reads the
victory politically: the oppressor's death opens Babylonian freedom and the
reign of Izdubar.

This is not a generic monster-slaying record. It is a gated sanctuary/tyrant
boundary: mouth-tempest guards the forest threshold; gate entry exposes the
agent to unknown battle; victory converts guarded regalia into public freedom.

No `sorry`, no new `axiom`.
-/

structure UnknownExpeditionRisk where
  battleUnknown : Bool := true
  expeditionUnknown : Bool := true
  longRoadAndReturnNamed : Bool := true
  shamasAidInvoked : Bool := true
  gateOfAssemblyOpened : Bool := true
deriving DecidableEq, Repr

def unknownExpeditionRisk : UnknownExpeditionRisk := {}

def expeditionRiskWitness (r : UnknownExpeditionRisk) : Prop :=
  r.battleUnknown = true ∧
  r.expeditionUnknown = true ∧
  r.longRoadAndReturnNamed = true ∧
  r.shamasAidInvoked = true ∧
  r.gateOfAssemblyOpened = true

structure ForestGateSanctuary where
  pineCedarForestEnclosed : Bool := true
  barrierOrWallPresent : Bool := true
  gateOpenedByHeabaniAndIzdubar : Bool := true
  seatOfGodsNamed : Bool := true
  sanctuaryOfAngelsNamed : Bool := true
  goodShadowAndFruitNamed : Bool := true
deriving DecidableEq, Repr

def forestGateSanctuary : ForestGateSanctuary := {}

def gatedForestSanctuary (f : ForestGateSanctuary) : Prop :=
  f.pineCedarForestEnclosed = true ∧
  f.barrierOrWallPresent = true ∧
  f.gateOpenedByHeabaniAndIzdubar = true ∧
  f.seatOfGodsNamed = true ∧
  f.sanctuaryOfAngelsNamed = true ∧
  f.goodShadowAndFruitNamed = true

structure HumbabaMouthTempest where
  humbabaPoursTempestFromMouth : Bool := true
  hearsForestGateOpen : Bool := true
  takesFearWeapon : Bool := true
  waitsInForestPath : Bool := true
  corpseSurroundedByBirdsOfPrey : Bool := true
deriving DecidableEq, Repr

def humbabaMouthTempest : HumbabaMouthTempest := {}

def mouthTempestGatekeeper (h : HumbabaMouthTempest) : Prop :=
  h.humbabaPoursTempestFromMouth = true ∧
  h.hearsForestGateOpen = true ∧
  h.takesFearWeapon = true ∧
  h.waitsInForestPath = true ∧
  h.corpseSurroundedByBirdsOfPrey = true

structure OppressorBoundaryConversion where
  humbabaConqueredAndSlain : Bool := true
  goodsAndRegaliaTaken : Bool := true
  oppressorDeathNamed : Bool := true
  babylonianFreedomProclaimed : Bool := true
  reignOfIzdubarFollows : Bool := true
deriving DecidableEq, Repr

def oppressorBoundaryConversion : OppressorBoundaryConversion := {}

def tyrantBoundaryConvertsToFreedom (o : OppressorBoundaryConversion) : Prop :=
  o.humbabaConqueredAndSlain = true ∧
  o.goodsAndRegaliaTaken = true ∧
  o.oppressorDeathNamed = true ∧
  o.babylonianFreedomProclaimed = true ∧
  o.reignOfIzdubarFollows = true

theorem humbaba_expedition_risk :
    expeditionRiskWitness unknownExpeditionRisk := by
  unfold expeditionRiskWitness unknownExpeditionRisk
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem humbaba_gated_forest_sanctuary :
    gatedForestSanctuary forestGateSanctuary := by
  unfold gatedForestSanctuary forestGateSanctuary
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem humbaba_mouth_tempest_gatekeeper :
    mouthTempestGatekeeper humbabaMouthTempest := by
  unfold mouthTempestGatekeeper humbabaMouthTempest
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem humbaba_tyrant_boundary_converts_to_freedom :
    tyrantBoundaryConvertsToFreedom oppressorBoundaryConversion := by
  unfold tyrantBoundaryConvertsToFreedom oppressorBoundaryConversion
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem humbaba_inherits_wind_mouth_mechanic :
    SevenWindsContainmentDeepWitness.timedMouthInjection
      SevenWindsContainmentDeepWitness.mouthClosureInjection ∧
    mouthTempestGatekeeper humbabaMouthTempest := by
  exact ⟨SevenWindsContainmentDeepWitness.seven_wind_mouth_injection,
    humbaba_mouth_tempest_gatekeeper⟩

theorem humbaba_forest_gate_tempest_witness :
    expeditionRiskWitness unknownExpeditionRisk ∧
    gatedForestSanctuary forestGateSanctuary ∧
    mouthTempestGatekeeper humbabaMouthTempest ∧
    tyrantBoundaryConvertsToFreedom oppressorBoundaryConversion := by
  exact ⟨humbaba_expedition_risk,
    humbaba_gated_forest_sanctuary,
    humbaba_mouth_tempest_gatekeeper,
    humbaba_tyrant_boundary_converts_to_freedom⟩

end HumbabaForestGateTempestWitness
end Gnosis.Witnesses.Chaldean
