import Gnosis.Witnesses.Chaldean.DelugeSeventhDayBirdProbeWitness
import Gnosis.Witnesses.Chaldean.HeaAlternativeJudgmentWitness
import Gnosis.Witnesses.Chaldean.IshtarSevenGateRegaliaBodyWitness
import Gnosis.Witnesses.Chaldean.MummuTiamatuWaterChaosCarrierWitness

namespace Gnosis.Witnesses.Chaldean
namespace IzdubarCleansingCloakHealthWitness

/-!
# Izdubar Cleansing Cloak Health Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Chapter XII,
the post-deluge Hasisadra/Izdubar/Urhamsi healing sequence.

This passage gives a recovery protocol rather than a mere blessing. The health
seeker receives a six-days/seven-nights trial; the road is laid on him like a
storm; the wife says to clothe him and send him away; seven clothing acts free
him. Then Urhamsi takes the diseased body to be cleansed: disease turns to
beauty in water, illness is cast off, the sea carries it away, health covers
the skin, hair is restored, and the cloak remains as return-road state.

No `sorry`, no new `axiom`.
-/

structure TrialBeforeHealth where
  healthSoughtAndAsked : Bool := true
  sixDaysNamed : Bool := true
  sevenNightsNamed : Bool := true
  stormWayLaidOnSeeker : Bool := true
  wifeCommandsClothingAndPeacefulReturn : Bool := true
deriving DecidableEq, Repr

def trialBeforeHealth : TrialBeforeHealth := {}

def healthTrialWitness (t : TrialBeforeHealth) : Prop :=
  t.healthSoughtAndAsked = true ∧
  t.sixDaysNamed = true ∧
  t.sevenNightsNamed = true ∧
  t.stormWayLaidOnSeeker = true ∧
  t.wifeCommandsClothingAndPeacefulReturn = true

structure SevenfoldClothingRelease where
  kurummatPlacedOnHead : Bool := true
  firstSabusatNamed : Bool := true
  secondMussukatNamed : Bool := true
  thirdRadbatNamed : Bool := true
  fourthZikamanOpened : Bool := true
  fifthCloakPlaced : Bool := true
  sixthBassatNamed : Bool := true
  seventhMantleOrCloakFreesMan : Bool := true
deriving DecidableEq, Repr

def sevenfoldClothingRelease : SevenfoldClothingRelease := {}

def sevenClothingActsFree (s : SevenfoldClothingRelease) : Prop :=
  s.kurummatPlacedOnHead = true ∧
  s.firstSabusatNamed = true ∧
  s.secondMussukatNamed = true ∧
  s.thirdRadbatNamed = true ∧
  s.fourthZikamanOpened = true ∧
  s.fifthCloakPlaced = true ∧
  s.sixthBassatNamed = true ∧
  s.seventhMantleOrCloakFreesMan = true

structure WaterDiseaseExport where
  diseaseFillsBody : Bool := true
  illnessDestroysLimbStrength : Bool := true
  carriedToCleanse : Bool := true
  diseaseTurnsToBeautyInWater : Bool := true
  illnessCastOff : Bool := true
  seaCarriesIllnessAway : Bool := true
  healthCoversSkin : Bool := true
  hairRestored : Bool := true
deriving DecidableEq, Repr

def waterDiseaseExport : WaterDiseaseExport := {}

def waterExportsIllness (w : WaterDiseaseExport) : Prop :=
  w.diseaseFillsBody = true ∧
  w.illnessDestroysLimbStrength = true ∧
  w.carriedToCleanse = true ∧
  w.diseaseTurnsToBeautyInWater = true ∧
  w.illnessCastOff = true ∧
  w.seaCarriesIllnessAway = true ∧
  w.healthCoversSkin = true ∧
  w.hairRestored = true

structure ReturnRoadReintegration where
  roadBackToCountryNamed : Bool := true
  hangingCloakNotCastOff : Bool := true
  shipTouchesShore : Bool := true
  concealedStoryRevealed : Bool := true
  returnToErechNamed : Bool := true
  cityWallAndTempleBoundaryMeasured : Bool := true
deriving DecidableEq, Repr

def returnRoadReintegration : ReturnRoadReintegration := {}

def returnRoadRestoresPlace (r : ReturnRoadReintegration) : Prop :=
  r.roadBackToCountryNamed = true ∧
  r.hangingCloakNotCastOff = true ∧
  r.shipTouchesShore = true ∧
  r.concealedStoryRevealed = true ∧
  r.returnToErechNamed = true ∧
  r.cityWallAndTempleBoundaryMeasured = true

theorem izdubar_health_trial :
    healthTrialWitness trialBeforeHealth := by
  unfold healthTrialWitness trialBeforeHealth
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem izdubar_seven_clothing_acts_free :
    sevenClothingActsFree sevenfoldClothingRelease := by
  unfold sevenClothingActsFree sevenfoldClothingRelease
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem izdubar_water_exports_illness :
    waterExportsIllness waterDiseaseExport := by
  unfold waterExportsIllness waterDiseaseExport
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem izdubar_return_road_restores_place :
    returnRoadRestoresPlace returnRoadReintegration := by
  unfold returnRoadRestoresPlace returnRoadReintegration
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem izdubar_inherits_chaldean_regalia_body_ledger :
    IshtarSevenGateRegaliaBodyWitness.gateIndexedBodyLedger
      IshtarSevenGateRegaliaBodyWitness.bodyLedgerGateProtocol ∧
    sevenClothingActsFree sevenfoldClothingRelease := by
  exact ⟨IshtarSevenGateRegaliaBodyWitness.ishtar_gate_indexed_body_ledger,
    izdubar_seven_clothing_acts_free⟩

theorem izdubar_water_repair_inherits_sea_carrier :
    MummuTiamatuWaterChaosCarrierWitness.seaFriendFoeTaming
      MummuTiamatuWaterChaosCarrierWitness.seaTamingAmbivalence ∧
    waterExportsIllness waterDiseaseExport := by
  exact ⟨MummuTiamatuWaterChaosCarrierWitness.mummu_tiamatu_sea_friend_foe_taming,
    izdubar_water_exports_illness⟩

theorem izdubar_inherits_deluge_survivor_repair :
    HeaAlternativeJudgmentWitness.survivorCovenantRepair
      HeaAlternativeJudgmentWitness.covenantAfterCorrection ∧
    DelugeSeventhDayBirdProbeWitness.shipPreservesState
      DelugeSeventhDayBirdProbeWitness.sealedShipCarrier ∧
    returnRoadRestoresPlace returnRoadReintegration := by
  exact ⟨HeaAlternativeJudgmentWitness.hea_survivor_covenant_repair,
    DelugeSeventhDayBirdProbeWitness.deluge_ship_preserves_state,
    izdubar_return_road_restores_place⟩

theorem izdubar_cleansing_cloak_health_witness :
    healthTrialWitness trialBeforeHealth ∧
    sevenClothingActsFree sevenfoldClothingRelease ∧
    waterExportsIllness waterDiseaseExport ∧
    returnRoadRestoresPlace returnRoadReintegration := by
  exact ⟨izdubar_health_trial,
    izdubar_seven_clothing_acts_free,
    izdubar_water_exports_illness,
    izdubar_return_road_restores_place⟩

end IzdubarCleansingCloakHealthWitness
end Gnosis.Witnesses.Chaldean
