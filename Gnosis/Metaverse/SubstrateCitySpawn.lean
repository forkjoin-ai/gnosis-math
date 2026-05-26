import Gnosis.HotellingModel
import Gnosis.SocialDynamicsHooke

namespace Gnosis
namespace Metaverse

/-!
# Substrate and social-density city spawning

This module is the procedural world-generation rule layer.  Objects can only be
placed on substrates that support their energy mode.  Biomes restrict which
substrates and object families are available.  City substrates such as concrete
spawn only at social-density moments where humans collect enough interaction
energy to produce civic substrate.

The Hotelling import anchors service placement on the repository's discrete city
line; the social-dynamics import marks this as part of the broader body/social
formalization surface.
-/

inductive ProceduralObject where
  | tree
  | fern
  | human
  | animal
  | rock
  | road
  | serviceCenter
deriving DecidableEq, Repr

inductive Substrate where
  | soil
  | forestFloor
  | concrete
  | asphalt
  | bedrock
  | alpinePeak
  | water
deriving DecidableEq, Repr

inductive Biome where
  | forest
  | alpine
  | city
  | coastal
  | desert
  | wetland
deriving DecidableEq, Repr

inductive EnergyMode where
  | photosyntheticRooted
  | internalMetabolic
  | structuralInert
  | civicNetwork
deriving DecidableEq, Repr

inductive TransitionMediator where
  | none
  | road
  | bridge
  | tunnel
deriving DecidableEq, Repr

def objectEnergyMode : ProceduralObject -> EnergyMode
  | ProceduralObject.tree => EnergyMode.photosyntheticRooted
  | ProceduralObject.fern => EnergyMode.photosyntheticRooted
  | ProceduralObject.human => EnergyMode.internalMetabolic
  | ProceduralObject.animal => EnergyMode.internalMetabolic
  | ProceduralObject.rock => EnergyMode.structuralInert
  | ProceduralObject.road => EnergyMode.civicNetwork
  | ProceduralObject.serviceCenter => EnergyMode.civicNetwork

def placementAllowed
    (object : ProceduralObject)
    (substrate : Substrate) : Bool :=
  match object, substrate with
  | ProceduralObject.tree, Substrate.soil => true
  | ProceduralObject.tree, Substrate.forestFloor => true
  | ProceduralObject.tree, _ => false
  | ProceduralObject.fern, Substrate.forestFloor => true
  | ProceduralObject.fern, Substrate.soil => true
  | ProceduralObject.fern, _ => false
  | ProceduralObject.human, Substrate.concrete => true
  | ProceduralObject.human, Substrate.asphalt => true
  | ProceduralObject.human, Substrate.soil => true
  | ProceduralObject.human, _ => false
  | ProceduralObject.animal, Substrate.soil => true
  | ProceduralObject.animal, Substrate.forestFloor => true
  | ProceduralObject.animal, _ => false
  | ProceduralObject.rock, Substrate.bedrock => true
  | ProceduralObject.rock, Substrate.alpinePeak => true
  | ProceduralObject.rock, _ => false
  | ProceduralObject.road, Substrate.asphalt => true
  | ProceduralObject.road, Substrate.concrete => true
  | ProceduralObject.road, _ => false
  | ProceduralObject.serviceCenter, Substrate.concrete => true
  | ProceduralObject.serviceCenter, Substrate.asphalt => true
  | ProceduralObject.serviceCenter, _ => false

def substrateAllowedInBiome
    (substrate : Substrate)
    (biome : Biome) : Bool :=
  match substrate, biome with
  | Substrate.soil, Biome.forest => true
  | Substrate.forestFloor, Biome.forest => true
  | Substrate.bedrock, Biome.forest => true
  | Substrate.alpinePeak, Biome.alpine => true
  | Substrate.bedrock, Biome.alpine => true
  | Substrate.concrete, Biome.city => true
  | Substrate.asphalt, Biome.city => true
  | Substrate.soil, Biome.coastal => true
  | Substrate.water, Biome.coastal => true
  | Substrate.bedrock, Biome.coastal => true
  | Substrate.soil, Biome.desert => true
  | Substrate.bedrock, Biome.desert => true
  | Substrate.soil, Biome.wetland => true
  | Substrate.water, Biome.wetland => true
  | Substrate.forestFloor, Biome.wetland => true
  | _, _ => false

def objectAllowedInBiome
    (object : ProceduralObject)
    (biome : Biome) : Bool :=
  match object, biome with
  | ProceduralObject.tree, Biome.forest => true
  | ProceduralObject.fern, Biome.forest => true
  | ProceduralObject.fern, Biome.wetland => true
  | ProceduralObject.human, Biome.city => true
  | ProceduralObject.human, Biome.coastal => true
  | ProceduralObject.human, Biome.desert => true
  | ProceduralObject.animal, Biome.forest => true
  | ProceduralObject.animal, Biome.coastal => true
  | ProceduralObject.animal, Biome.desert => true
  | ProceduralObject.animal, Biome.wetland => true
  | ProceduralObject.rock, _ => true
  | ProceduralObject.road, Biome.city => true
  | ProceduralObject.serviceCenter, Biome.city => true
  | _, _ => false

def objectSubstrateAllowedInBiome
    (object : ProceduralObject)
    (substrate : Substrate)
    (biome : Biome) : Bool :=
  objectAllowedInBiome object biome &&
    substrateAllowedInBiome substrate biome &&
    placementAllowed object substrate

structure BiomeCompatibility where
  biome : Biome
  substrates : List Substrate
  objects : List ProceduralObject
deriving DecidableEq, Repr

def forestBiomeCompatibility : BiomeCompatibility :=
  { biome := Biome.forest
    substrates := [Substrate.soil, Substrate.forestFloor, Substrate.bedrock]
    objects := [ProceduralObject.tree, ProceduralObject.fern,
      ProceduralObject.animal, ProceduralObject.rock] }

def alpineBiomeCompatibility : BiomeCompatibility :=
  { biome := Biome.alpine
    substrates := [Substrate.alpinePeak, Substrate.bedrock]
    objects := [ProceduralObject.rock] }

def cityBiomeCompatibility : BiomeCompatibility :=
  { biome := Biome.city
    substrates := [Substrate.concrete, Substrate.asphalt]
    objects := [ProceduralObject.human, ProceduralObject.road,
      ProceduralObject.serviceCenter] }

def coastalBiomeCompatibility : BiomeCompatibility :=
  { biome := Biome.coastal
    substrates := [Substrate.soil, Substrate.water, Substrate.bedrock]
    objects := [ProceduralObject.human, ProceduralObject.animal,
      ProceduralObject.rock] }

def desertBiomeCompatibility : BiomeCompatibility :=
  { biome := Biome.desert
    substrates := [Substrate.soil, Substrate.bedrock]
    objects := [ProceduralObject.human, ProceduralObject.animal,
      ProceduralObject.rock] }

def wetlandBiomeCompatibility : BiomeCompatibility :=
  { biome := Biome.wetland
    substrates := [Substrate.soil, Substrate.water, Substrate.forestFloor]
    objects := [ProceduralObject.fern, ProceduralObject.animal,
      ProceduralObject.rock] }

def biomeCompatibilityCatalog : List BiomeCompatibility :=
  [ forestBiomeCompatibility
  , alpineBiomeCompatibility
  , cityBiomeCompatibility
  , coastalBiomeCompatibility
  , desertBiomeCompatibility
  , wetlandBiomeCompatibility
  ]

def biomeTrace : List Biome :=
  biomeCompatibilityCatalog.map BiomeCompatibility.biome

def biomeSubstrateCounts : List Nat :=
  biomeCompatibilityCatalog.map
    (fun compatibility => compatibility.substrates.length)

def biomeObjectCounts : List Nat :=
  biomeCompatibilityCatalog.map
    (fun compatibility => compatibility.objects.length)

structure SocialDensityMoment where
  humans : Nat
  interactions : Nat
  collection : Nat
  threshold : Nat
deriving DecidableEq, Repr

def socialDensityScore (moment : SocialDensityMoment) : Nat :=
  moment.humans + moment.interactions + moment.collection

def canSpawnConcrete (moment : SocialDensityMoment) : Bool :=
  moment.threshold <= socialDensityScore moment

def lowSocialDensityMoment : SocialDensityMoment :=
  { humans := 1, interactions := 1, collection := 0, threshold := 5 }

def citySocialDensityMoment : SocialDensityMoment :=
  { humans := 2, interactions := 2, collection := 2, threshold := 5 }

def highSocialDensityMoment : SocialDensityMoment :=
  { humans := 4, interactions := 3, collection := 3, threshold := 5 }

def socialDensityMoments : List SocialDensityMoment :=
  [lowSocialDensityMoment, citySocialDensityMoment, highSocialDensityMoment]

def socialDensitySpawnFlags : List Bool :=
  socialDensityMoments.map canSpawnConcrete

def concreteSpawnYieldsCitySubstrate
    (moment : SocialDensityMoment) : Bool :=
  canSpawnConcrete moment &&
    objectSubstrateAllowedInBiome ProceduralObject.human
      Substrate.concrete Biome.city

def cityConcreteSpawnCertified : Prop :=
  socialDensitySpawnFlags = [false, true, true] /\
    concreteSpawnYieldsCitySubstrate citySocialDensityMoment = true /\
    concreteSpawnYieldsCitySubstrate highSocialDensityMoment = true /\
    concreteSpawnYieldsCitySubstrate lowSocialDensityMoment = false /\
    HotellingModel.leftDemand4 2 2 = 5

def biomeCompatibilityCertified : Prop :=
  biomeTrace =
    [Biome.forest, Biome.alpine, Biome.city, Biome.coastal,
      Biome.desert, Biome.wetland] /\
    biomeSubstrateCounts = [3, 2, 2, 3, 2, 3] /\
    biomeObjectCounts = [4, 1, 3, 3, 3, 3] /\
    objectSubstrateAllowedInBiome ProceduralObject.tree
      Substrate.forestFloor Biome.forest = true /\
    objectSubstrateAllowedInBiome ProceduralObject.tree
      Substrate.alpinePeak Biome.alpine = false /\
    objectSubstrateAllowedInBiome ProceduralObject.human
      Substrate.concrete Biome.city = true /\
    objectSubstrateAllowedInBiome ProceduralObject.serviceCenter
      Substrate.concrete Biome.city = true /\
    objectSubstrateAllowedInBiome ProceduralObject.fern
      Substrate.forestFloor Biome.wetland = true

theorem biome_compatibility_certified :
    biomeCompatibilityCertified := by
  simp [biomeCompatibilityCertified, biomeTrace, biomeSubstrateCounts,
    biomeObjectCounts, biomeCompatibilityCatalog,
    forestBiomeCompatibility, alpineBiomeCompatibility,
    cityBiomeCompatibility, coastalBiomeCompatibility,
    desertBiomeCompatibility, wetlandBiomeCompatibility,
    objectSubstrateAllowedInBiome, objectAllowedInBiome,
    substrateAllowedInBiome, placementAllowed]

theorem city_concrete_spawn_certified :
    cityConcreteSpawnCertified := by
  simp [cityConcreteSpawnCertified, socialDensitySpawnFlags,
    socialDensityMoments, canSpawnConcrete, socialDensityScore,
    lowSocialDensityMoment, citySocialDensityMoment,
    highSocialDensityMoment, concreteSpawnYieldsCitySubstrate,
    objectSubstrateAllowedInBiome, objectAllowedInBiome,
    substrateAllowedInBiome, placementAllowed,
    HotellingModel.center_left_demand4_full]

theorem trees_do_not_generate_on_alpine_peaks :
    objectSubstrateAllowedInBiome ProceduralObject.tree
      Substrate.alpinePeak Biome.alpine = false := by
  simp [objectSubstrateAllowedInBiome, objectAllowedInBiome,
    substrateAllowedInBiome, placementAllowed]

theorem humans_collecting_can_spawn_concrete :
    concreteSpawnYieldsCitySubstrate citySocialDensityMoment = true := by
  simp [concreteSpawnYieldsCitySubstrate, canSpawnConcrete,
    socialDensityScore, citySocialDensityMoment,
    objectSubstrateAllowedInBiome, objectAllowedInBiome,
    substrateAllowedInBiome, placementAllowed]

end Metaverse
end Gnosis
