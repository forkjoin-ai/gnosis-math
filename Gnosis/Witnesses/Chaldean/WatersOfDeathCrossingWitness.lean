import Gnosis.Witnesses.Chaldean.HeabaniEarthTakesLamentWitness
import Gnosis.Witnesses.Chaldean.IzdubarCleansingCloakHealthWitness
import Gnosis.Witnesses.Chaldean.IzdubarErechReturnCityBoundaryWitness
import Gnosis.Witnesses.Chaldean.MummuTiamatuWaterChaosCarrierWitness

namespace Gnosis.Witnesses.Chaldean
namespace WatersOfDeathCrossingWitness

/-!
# Waters Of Death Crossing Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Tablet X-XII
material and conclusion summary of Izdubar's journey to Hasisadra.

This is not an ordinary sea voyage. Izdubar reaches the sea-coast diseased and
marked by affliction; Siduri/Sabitu close the gate; Urhamsi becomes boatman;
the ship route approaches the region of Hasisadra; the dwelling of the blessed
is surrounded by waters of death which must be crossed without being enclosed.

Across the boundary the witness becomes conversational and therapeutic: Ragmu
receives the Heabani grief discourse, Hasisadra discloses the Deluge and the
judgment of the gods, then the health protocol sends Izdubar back by Urhamsi.
Water first gates death, then carries illness away, then the return to Erech
restores civic boundary.

No `sorry`, no new `axiom`.
-/

structure SeaGateRefusal where
  diseaseAndAfflictionMarked : Bool := true
  distantPathDesired : Bool := true
  siduriSabituDwellBesideSea : Bool := true
  gateClosedAgainstIzdubar : Bool := true
  routeRequiresMediatedAccess : Bool := true
deriving DecidableEq, Repr

def seaGateRefusal : SeaGateRefusal := {}

def seaGateBlocksUnmediatedPassage (s : SeaGateRefusal) : Prop :=
  s.diseaseAndAfflictionMarked = true ∧
  s.distantPathDesired = true ∧
  s.siduriSabituDwellBesideSea = true ∧
  s.gateClosedAgainstIzdubar = true ∧
  s.routeRequiresMediatedAccess = true

structure UrhamsiBoatmanCrossing where
  urhamsiNamedBoatman : Bool := true
  boatJourneyBegins : Bool := true
  deathShipFragmentPresent : Bool := true
  crossingRequiresCarriage : Bool := true
  watersOfDeathNamed : Bool := true
  watersMustNotEnclose : Bool := true
deriving DecidableEq, Repr

def urhamsiBoatmanCrossing : UrhamsiBoatmanCrossing := {}

def boatmanMediatesWatersOfDeath (u : UrhamsiBoatmanCrossing) : Prop :=
  u.urhamsiNamedBoatman = true ∧
  u.boatJourneyBegins = true ∧
  u.deathShipFragmentPresent = true ∧
  u.crossingRequiresCarriage = true ∧
  u.watersOfDeathNamed = true ∧
  u.watersMustNotEnclose = true

structure BlessedRegionDisclosure where
  regionOfBlessedSought : Bool := true
  dwellingOfBlessedWaterBounded : Bool := true
  ragmuReceivesHeabaniConversation : Bool := true
  hasisadraContinuesConversation : Bool := true
  delugeDisclosedAcrossBoundary : Bool := true
  deathAndLifeKnowledgeNamed : Bool := true
deriving DecidableEq, Repr

def blessedRegionDisclosure : BlessedRegionDisclosure := {}

def boundaryCrossingDisclosesHiddenKnowledge (b : BlessedRegionDisclosure) : Prop :=
  b.regionOfBlessedSought = true ∧
  b.dwellingOfBlessedWaterBounded = true ∧
  b.ragmuReceivesHeabaniConversation = true ∧
  b.hasisadraContinuesConversation = true ∧
  b.delugeDisclosedAcrossBoundary = true ∧
  b.deathAndLifeKnowledgeNamed = true

structure ReturnFromDeathWater where
  healedAfterDisclosure : Bool := true
  urhamsiCarriesToCleanse : Bool := true
  illnessExportedBySea : Bool := true
  returnsWithUrhamsiToErech : Bool := true
  mournsHeabaniAgain : Bool := true
  heabaniGhostRisesFromGround : Bool := true
deriving DecidableEq, Repr

def returnFromDeathWater : ReturnFromDeathWater := {}

def deathWaterCrossingReturnsWitness (r : ReturnFromDeathWater) : Prop :=
  r.healedAfterDisclosure = true ∧
  r.urhamsiCarriesToCleanse = true ∧
  r.illnessExportedBySea = true ∧
  r.returnsWithUrhamsiToErech = true ∧
  r.mournsHeabaniAgain = true ∧
  r.heabaniGhostRisesFromGround = true

theorem waters_sea_gate_blocks_unmediated_passage :
    seaGateBlocksUnmediatedPassage seaGateRefusal := by
  unfold seaGateBlocksUnmediatedPassage seaGateRefusal
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem waters_boatman_mediates_waters_of_death :
    boatmanMediatesWatersOfDeath urhamsiBoatmanCrossing := by
  unfold boatmanMediatesWatersOfDeath urhamsiBoatmanCrossing
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem waters_boundary_crossing_discloses_hidden_knowledge :
    boundaryCrossingDisclosesHiddenKnowledge blessedRegionDisclosure := by
  unfold boundaryCrossingDisclosesHiddenKnowledge blessedRegionDisclosure
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem waters_death_water_crossing_returns_witness :
    deathWaterCrossingReturnsWitness returnFromDeathWater := by
  unfold deathWaterCrossingReturnsWitness returnFromDeathWater
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem waters_inherits_water_friend_foe :
    MummuTiamatuWaterChaosCarrierWitness.seaFriendFoeTaming
      MummuTiamatuWaterChaosCarrierWitness.seaTamingAmbivalence ∧
    boatmanMediatesWatersOfDeath urhamsiBoatmanCrossing := by
  exact ⟨MummuTiamatuWaterChaosCarrierWitness.mummu_tiamatu_sea_friend_foe_taming,
    waters_boatman_mediates_waters_of_death⟩

theorem waters_inherits_cleansing_return :
    IzdubarCleansingCloakHealthWitness.waterExportsIllness
      IzdubarCleansingCloakHealthWitness.waterDiseaseExport ∧
    IzdubarErechReturnCityBoundaryWitness.erechBoundaryMeasured
      IzdubarErechReturnCityBoundaryWitness.cityBoundarySurvey ∧
    deathWaterCrossingReturnsWitness returnFromDeathWater := by
  exact ⟨IzdubarCleansingCloakHealthWitness.izdubar_water_exports_illness,
    IzdubarErechReturnCityBoundaryWitness.izdubar_erech_boundary_measured,
    waters_death_water_crossing_returns_witness⟩

theorem waters_inherits_heabani_death_disclosure :
    HeabaniEarthTakesLamentWitness.earthTakesByExclusion
      HeabaniEarthTakesLamentWitness.earthTakesExclusion ∧
    boundaryCrossingDisclosesHiddenKnowledge blessedRegionDisclosure := by
  exact ⟨HeabaniEarthTakesLamentWitness.heabani_earth_takes_by_exclusion,
    waters_boundary_crossing_discloses_hidden_knowledge⟩

theorem waters_of_death_crossing_witness :
    seaGateBlocksUnmediatedPassage seaGateRefusal ∧
    boatmanMediatesWatersOfDeath urhamsiBoatmanCrossing ∧
    boundaryCrossingDisclosesHiddenKnowledge blessedRegionDisclosure ∧
    deathWaterCrossingReturnsWitness returnFromDeathWater := by
  exact ⟨waters_sea_gate_blocks_unmediated_passage,
    waters_boatman_mediates_waters_of_death,
    waters_boundary_crossing_discloses_hidden_knowledge,
    waters_death_water_crossing_returns_witness⟩

end WatersOfDeathCrossingWitness
end Gnosis.Witnesses.Chaldean
