import Gnosis.ImpossibleFireworkShapes
import Gnosis.TreeShapes
import Gnosis.GeoShapes
import Gnosis.Metaverse.SubstrateCitySpawn

namespace Gnosis
namespace Metaverse

/-!
# Primitive Phyle shapes

This module is the finite primitive-shape contract for procedural 3D scene
generation.  It aligns the existing natural, botanical, geologic, substrate,
civic, and embodied object catalogs under one Phyle-carried surface.
-/

inductive PrimitiveShapeFamily where
  | nature
  | botanical
  | geologic
  | substrate
  | civic
  | embodied
deriving DecidableEq, Repr

inductive PrimitiveShapeRole where
  | display
  | vegetation
  | terrain
  | substrate
  | infrastructure
  | body
deriving DecidableEq, Repr

inductive PrimitiveShapeName where
  | sphere
  | hexagon
  | torus
  | vortex
  | spiral
  | dendritic
  | fractal
  | catenary
  | octahedron
  | prism
  | dodecahedron
  | undulation
  | streamline
  | radialSymmetry
  | bilateralSymmetry
  | oak
  | pine
  | maple
  | willow
  | birch
  | cedar
  | cypress
  | palm
  | baobab
  | redwood
  | spruce
  | fir
  | elm
  | aspen
  | fern
  | boulder
  | screeField
  | sedimentLayer
  | quartzPrism
  | diamondOctahedron
  | geode
  | continent
  | island
  | peninsula
  | isthmus
  | mountainRange
  | ridge
  | volcano
  | plateau
  | basin
  | valley
  | canyon
  | delta
  | coastline
  | fjord
  | archipelago
  | soil
  | forestFloor
  | concrete
  | asphalt
  | bedrock
  | alpinePeak
  | water
  | road
  | serviceCenter
  | human
  | animal
deriving DecidableEq, Repr

structure PrimitiveShapeSpec where
  family : PrimitiveShapeFamily
  role : PrimitiveShapeRole
  name : PrimitiveShapeName
  phyleCarried : Bool
deriving DecidableEq, Repr

def primitiveShape
    (family : PrimitiveShapeFamily)
    (role : PrimitiveShapeRole)
    (name : PrimitiveShapeName) : PrimitiveShapeSpec :=
  { family, role, name, phyleCarried := true }

def naturePrimitiveCatalog : List PrimitiveShapeSpec :=
  [ primitiveShape PrimitiveShapeFamily.nature PrimitiveShapeRole.display
      PrimitiveShapeName.fractal
  , primitiveShape PrimitiveShapeFamily.nature PrimitiveShapeRole.display
      PrimitiveShapeName.spiral
  , primitiveShape PrimitiveShapeFamily.nature PrimitiveShapeRole.display
      PrimitiveShapeName.dendritic
  , primitiveShape PrimitiveShapeFamily.nature PrimitiveShapeRole.display
      PrimitiveShapeName.sphere
  , primitiveShape PrimitiveShapeFamily.nature PrimitiveShapeRole.display
      PrimitiveShapeName.hexagon
  , primitiveShape PrimitiveShapeFamily.nature PrimitiveShapeRole.display
      PrimitiveShapeName.catenary
  , primitiveShape PrimitiveShapeFamily.nature PrimitiveShapeRole.display
      PrimitiveShapeName.octahedron
  , primitiveShape PrimitiveShapeFamily.nature PrimitiveShapeRole.display
      PrimitiveShapeName.prism
  , primitiveShape PrimitiveShapeFamily.nature PrimitiveShapeRole.display
      PrimitiveShapeName.dodecahedron
  , primitiveShape PrimitiveShapeFamily.nature PrimitiveShapeRole.display
      PrimitiveShapeName.vortex
  , primitiveShape PrimitiveShapeFamily.nature PrimitiveShapeRole.display
      PrimitiveShapeName.undulation
  , primitiveShape PrimitiveShapeFamily.nature PrimitiveShapeRole.display
      PrimitiveShapeName.streamline
  , primitiveShape PrimitiveShapeFamily.nature PrimitiveShapeRole.display
      PrimitiveShapeName.radialSymmetry
  , primitiveShape PrimitiveShapeFamily.nature PrimitiveShapeRole.display
      PrimitiveShapeName.bilateralSymmetry
  , primitiveShape PrimitiveShapeFamily.nature PrimitiveShapeRole.display
      PrimitiveShapeName.torus
  ]

def botanicalPrimitiveCatalog : List PrimitiveShapeSpec :=
  [ primitiveShape PrimitiveShapeFamily.botanical PrimitiveShapeRole.vegetation
      PrimitiveShapeName.oak
  , primitiveShape PrimitiveShapeFamily.botanical PrimitiveShapeRole.vegetation
      PrimitiveShapeName.pine
  , primitiveShape PrimitiveShapeFamily.botanical PrimitiveShapeRole.vegetation
      PrimitiveShapeName.maple
  , primitiveShape PrimitiveShapeFamily.botanical PrimitiveShapeRole.vegetation
      PrimitiveShapeName.willow
  , primitiveShape PrimitiveShapeFamily.botanical PrimitiveShapeRole.vegetation
      PrimitiveShapeName.birch
  , primitiveShape PrimitiveShapeFamily.botanical PrimitiveShapeRole.vegetation
      PrimitiveShapeName.cedar
  , primitiveShape PrimitiveShapeFamily.botanical PrimitiveShapeRole.vegetation
      PrimitiveShapeName.cypress
  , primitiveShape PrimitiveShapeFamily.botanical PrimitiveShapeRole.vegetation
      PrimitiveShapeName.palm
  , primitiveShape PrimitiveShapeFamily.botanical PrimitiveShapeRole.vegetation
      PrimitiveShapeName.baobab
  , primitiveShape PrimitiveShapeFamily.botanical PrimitiveShapeRole.vegetation
      PrimitiveShapeName.redwood
  , primitiveShape PrimitiveShapeFamily.botanical PrimitiveShapeRole.vegetation
      PrimitiveShapeName.spruce
  , primitiveShape PrimitiveShapeFamily.botanical PrimitiveShapeRole.vegetation
      PrimitiveShapeName.fir
  , primitiveShape PrimitiveShapeFamily.botanical PrimitiveShapeRole.vegetation
      PrimitiveShapeName.elm
  , primitiveShape PrimitiveShapeFamily.botanical PrimitiveShapeRole.vegetation
      PrimitiveShapeName.aspen
  , primitiveShape PrimitiveShapeFamily.botanical PrimitiveShapeRole.vegetation
      PrimitiveShapeName.fern
  ]

def geologicPrimitiveCatalog : List PrimitiveShapeSpec :=
  [ primitiveShape PrimitiveShapeFamily.geologic PrimitiveShapeRole.terrain
      PrimitiveShapeName.boulder
  , primitiveShape PrimitiveShapeFamily.geologic PrimitiveShapeRole.terrain
      PrimitiveShapeName.screeField
  , primitiveShape PrimitiveShapeFamily.geologic PrimitiveShapeRole.terrain
      PrimitiveShapeName.sedimentLayer
  , primitiveShape PrimitiveShapeFamily.geologic PrimitiveShapeRole.terrain
      PrimitiveShapeName.quartzPrism
  , primitiveShape PrimitiveShapeFamily.geologic PrimitiveShapeRole.terrain
      PrimitiveShapeName.diamondOctahedron
  , primitiveShape PrimitiveShapeFamily.geologic PrimitiveShapeRole.terrain
      PrimitiveShapeName.geode
  , primitiveShape PrimitiveShapeFamily.geologic PrimitiveShapeRole.terrain
      PrimitiveShapeName.continent
  , primitiveShape PrimitiveShapeFamily.geologic PrimitiveShapeRole.terrain
      PrimitiveShapeName.island
  , primitiveShape PrimitiveShapeFamily.geologic PrimitiveShapeRole.terrain
      PrimitiveShapeName.peninsula
  , primitiveShape PrimitiveShapeFamily.geologic PrimitiveShapeRole.terrain
      PrimitiveShapeName.isthmus
  , primitiveShape PrimitiveShapeFamily.geologic PrimitiveShapeRole.terrain
      PrimitiveShapeName.mountainRange
  , primitiveShape PrimitiveShapeFamily.geologic PrimitiveShapeRole.terrain
      PrimitiveShapeName.ridge
  , primitiveShape PrimitiveShapeFamily.geologic PrimitiveShapeRole.terrain
      PrimitiveShapeName.volcano
  , primitiveShape PrimitiveShapeFamily.geologic PrimitiveShapeRole.terrain
      PrimitiveShapeName.plateau
  , primitiveShape PrimitiveShapeFamily.geologic PrimitiveShapeRole.terrain
      PrimitiveShapeName.basin
  , primitiveShape PrimitiveShapeFamily.geologic PrimitiveShapeRole.terrain
      PrimitiveShapeName.valley
  , primitiveShape PrimitiveShapeFamily.geologic PrimitiveShapeRole.terrain
      PrimitiveShapeName.canyon
  , primitiveShape PrimitiveShapeFamily.geologic PrimitiveShapeRole.terrain
      PrimitiveShapeName.delta
  , primitiveShape PrimitiveShapeFamily.geologic PrimitiveShapeRole.terrain
      PrimitiveShapeName.coastline
  , primitiveShape PrimitiveShapeFamily.geologic PrimitiveShapeRole.terrain
      PrimitiveShapeName.fjord
  , primitiveShape PrimitiveShapeFamily.geologic PrimitiveShapeRole.terrain
      PrimitiveShapeName.archipelago
  ]

def substratePrimitiveCatalog : List PrimitiveShapeSpec :=
  [ primitiveShape PrimitiveShapeFamily.substrate PrimitiveShapeRole.substrate
      PrimitiveShapeName.soil
  , primitiveShape PrimitiveShapeFamily.substrate PrimitiveShapeRole.substrate
      PrimitiveShapeName.forestFloor
  , primitiveShape PrimitiveShapeFamily.substrate PrimitiveShapeRole.substrate
      PrimitiveShapeName.concrete
  , primitiveShape PrimitiveShapeFamily.substrate PrimitiveShapeRole.substrate
      PrimitiveShapeName.asphalt
  , primitiveShape PrimitiveShapeFamily.substrate PrimitiveShapeRole.substrate
      PrimitiveShapeName.bedrock
  , primitiveShape PrimitiveShapeFamily.substrate PrimitiveShapeRole.substrate
      PrimitiveShapeName.alpinePeak
  , primitiveShape PrimitiveShapeFamily.substrate PrimitiveShapeRole.substrate
      PrimitiveShapeName.water
  ]

def civicPrimitiveCatalog : List PrimitiveShapeSpec :=
  [ primitiveShape PrimitiveShapeFamily.civic PrimitiveShapeRole.infrastructure
      PrimitiveShapeName.road
  , primitiveShape PrimitiveShapeFamily.civic PrimitiveShapeRole.infrastructure
      PrimitiveShapeName.serviceCenter
  ]

def embodiedPrimitiveCatalog : List PrimitiveShapeSpec :=
  [ primitiveShape PrimitiveShapeFamily.embodied PrimitiveShapeRole.body
      PrimitiveShapeName.human
  , primitiveShape PrimitiveShapeFamily.embodied PrimitiveShapeRole.body
      PrimitiveShapeName.animal
  ]

def primitiveShapeCatalog : List PrimitiveShapeSpec :=
  naturePrimitiveCatalog ++ botanicalPrimitiveCatalog ++
    geologicPrimitiveCatalog ++ substratePrimitiveCatalog ++
    civicPrimitiveCatalog ++ embodiedPrimitiveCatalog

def primitiveNameTrace : List PrimitiveShapeName :=
  primitiveShapeCatalog.map PrimitiveShapeSpec.name

def primitiveFamilyTrace : List PrimitiveShapeFamily :=
  primitiveShapeCatalog.map PrimitiveShapeSpec.family

def primitiveRoleTrace : List PrimitiveShapeRole :=
  primitiveShapeCatalog.map PrimitiveShapeSpec.role

def primitiveCarrierTrace : List Bool :=
  primitiveShapeCatalog.map PrimitiveShapeSpec.phyleCarried

def expectedPrimitiveNameTrace : List PrimitiveShapeName :=
  [ PrimitiveShapeName.fractal
  , PrimitiveShapeName.spiral
  , PrimitiveShapeName.dendritic
  , PrimitiveShapeName.sphere
  , PrimitiveShapeName.hexagon
  , PrimitiveShapeName.catenary
  , PrimitiveShapeName.octahedron
  , PrimitiveShapeName.prism
  , PrimitiveShapeName.dodecahedron
  , PrimitiveShapeName.vortex
  , PrimitiveShapeName.undulation
  , PrimitiveShapeName.streamline
  , PrimitiveShapeName.radialSymmetry
  , PrimitiveShapeName.bilateralSymmetry
  , PrimitiveShapeName.torus
  , PrimitiveShapeName.oak
  , PrimitiveShapeName.pine
  , PrimitiveShapeName.maple
  , PrimitiveShapeName.willow
  , PrimitiveShapeName.birch
  , PrimitiveShapeName.cedar
  , PrimitiveShapeName.cypress
  , PrimitiveShapeName.palm
  , PrimitiveShapeName.baobab
  , PrimitiveShapeName.redwood
  , PrimitiveShapeName.spruce
  , PrimitiveShapeName.fir
  , PrimitiveShapeName.elm
  , PrimitiveShapeName.aspen
  , PrimitiveShapeName.fern
  , PrimitiveShapeName.boulder
  , PrimitiveShapeName.screeField
  , PrimitiveShapeName.sedimentLayer
  , PrimitiveShapeName.quartzPrism
  , PrimitiveShapeName.diamondOctahedron
  , PrimitiveShapeName.geode
  , PrimitiveShapeName.continent
  , PrimitiveShapeName.island
  , PrimitiveShapeName.peninsula
  , PrimitiveShapeName.isthmus
  , PrimitiveShapeName.mountainRange
  , PrimitiveShapeName.ridge
  , PrimitiveShapeName.volcano
  , PrimitiveShapeName.plateau
  , PrimitiveShapeName.basin
  , PrimitiveShapeName.valley
  , PrimitiveShapeName.canyon
  , PrimitiveShapeName.delta
  , PrimitiveShapeName.coastline
  , PrimitiveShapeName.fjord
  , PrimitiveShapeName.archipelago
  , PrimitiveShapeName.soil
  , PrimitiveShapeName.forestFloor
  , PrimitiveShapeName.concrete
  , PrimitiveShapeName.asphalt
  , PrimitiveShapeName.bedrock
  , PrimitiveShapeName.alpinePeak
  , PrimitiveShapeName.water
  , PrimitiveShapeName.road
  , PrimitiveShapeName.serviceCenter
  , PrimitiveShapeName.human
  , PrimitiveShapeName.animal
  ]

def primitiveShapeCatalogCertified : Prop :=
  primitiveNameTrace = expectedPrimitiveNameTrace /\
    primitiveShapeCatalog.length = 62 /\
    primitiveCarrierTrace = List.replicate 62 true /\
    naturePrimitiveCatalog.length = impossibleFireworkShapeCatalog.length /\
    botanicalPrimitiveCatalog.length = botanicalShapeCatalog.length /\
    geologicPrimitiveCatalog.length = geoShapeCatalog.length

theorem primitive_shape_catalog_certified :
    primitiveShapeCatalogCertified := by
  simp [primitiveShapeCatalogCertified,
    primitiveNameTrace, primitiveCarrierTrace, primitiveShapeCatalog,
    naturePrimitiveCatalog, botanicalPrimitiveCatalog,
    geologicPrimitiveCatalog, substratePrimitiveCatalog, civicPrimitiveCatalog,
    embodiedPrimitiveCatalog, expectedPrimitiveNameTrace, primitiveShape,
    impossibleFireworkShapeCatalog, botanicalShapeCatalog, geoShapeCatalog]

theorem primitive_shape_names_unique :
    primitiveNameTrace.Nodup := by
  simp [primitiveNameTrace, primitiveShapeCatalog,
    naturePrimitiveCatalog, botanicalPrimitiveCatalog,
    geologicPrimitiveCatalog, substratePrimitiveCatalog, civicPrimitiveCatalog,
    embodiedPrimitiveCatalog, primitiveShape]

theorem all_primitives_are_phyle_carried :
    primitiveCarrierTrace = List.replicate primitiveShapeCatalog.length true := by
  simp [primitiveCarrierTrace, primitiveShapeCatalog,
    naturePrimitiveCatalog, botanicalPrimitiveCatalog,
    geologicPrimitiveCatalog, substratePrimitiveCatalog, civicPrimitiveCatalog,
    embodiedPrimitiveCatalog, primitiveShape]

theorem substrate_primitives_align_with_spawn_layer :
    substratePrimitiveCatalog.map PrimitiveShapeSpec.name =
      [ PrimitiveShapeName.soil
      , PrimitiveShapeName.forestFloor
      , PrimitiveShapeName.concrete
      , PrimitiveShapeName.asphalt
      , PrimitiveShapeName.bedrock
      , PrimitiveShapeName.alpinePeak
      , PrimitiveShapeName.water
      ] /\
    objectSubstrateAllowedInBiome ProceduralObject.tree
      Substrate.alpinePeak Biome.alpine = false /\
    objectSubstrateAllowedInBiome ProceduralObject.human
      Substrate.concrete Biome.city = true := by
  simp [substratePrimitiveCatalog, primitiveShape,
    objectSubstrateAllowedInBiome, objectAllowedInBiome,
    substrateAllowedInBiome, placementAllowed]

/-! ## Placement bridge -/

def primitiveObject? : PrimitiveShapeName -> Option ProceduralObject
  | PrimitiveShapeName.oak => some ProceduralObject.tree
  | PrimitiveShapeName.pine => some ProceduralObject.tree
  | PrimitiveShapeName.maple => some ProceduralObject.tree
  | PrimitiveShapeName.willow => some ProceduralObject.tree
  | PrimitiveShapeName.birch => some ProceduralObject.tree
  | PrimitiveShapeName.cedar => some ProceduralObject.tree
  | PrimitiveShapeName.cypress => some ProceduralObject.tree
  | PrimitiveShapeName.palm => some ProceduralObject.tree
  | PrimitiveShapeName.baobab => some ProceduralObject.tree
  | PrimitiveShapeName.redwood => some ProceduralObject.tree
  | PrimitiveShapeName.spruce => some ProceduralObject.tree
  | PrimitiveShapeName.fir => some ProceduralObject.tree
  | PrimitiveShapeName.elm => some ProceduralObject.tree
  | PrimitiveShapeName.aspen => some ProceduralObject.tree
  | PrimitiveShapeName.fern => some ProceduralObject.fern
  | PrimitiveShapeName.boulder => some ProceduralObject.rock
  | PrimitiveShapeName.screeField => some ProceduralObject.rock
  | PrimitiveShapeName.sedimentLayer => some ProceduralObject.rock
  | PrimitiveShapeName.quartzPrism => some ProceduralObject.rock
  | PrimitiveShapeName.diamondOctahedron => some ProceduralObject.rock
  | PrimitiveShapeName.geode => some ProceduralObject.rock
  | PrimitiveShapeName.mountainRange => some ProceduralObject.rock
  | PrimitiveShapeName.ridge => some ProceduralObject.rock
  | PrimitiveShapeName.volcano => some ProceduralObject.rock
  | PrimitiveShapeName.plateau => some ProceduralObject.rock
  | PrimitiveShapeName.road => some ProceduralObject.road
  | PrimitiveShapeName.serviceCenter => some ProceduralObject.serviceCenter
  | PrimitiveShapeName.human => some ProceduralObject.human
  | PrimitiveShapeName.animal => some ProceduralObject.animal
  | _ => none

def primitiveSubstrate? : PrimitiveShapeName -> Option Substrate
  | PrimitiveShapeName.soil => some Substrate.soil
  | PrimitiveShapeName.forestFloor => some Substrate.forestFloor
  | PrimitiveShapeName.concrete => some Substrate.concrete
  | PrimitiveShapeName.asphalt => some Substrate.asphalt
  | PrimitiveShapeName.bedrock => some Substrate.bedrock
  | PrimitiveShapeName.alpinePeak => some Substrate.alpinePeak
  | PrimitiveShapeName.water => some Substrate.water
  | _ => none

def primitivePlacementAllowed
    (objectPrimitive : PrimitiveShapeName)
    (substratePrimitive : PrimitiveShapeName)
    (biome : Biome) : Bool :=
  match primitiveObject? objectPrimitive, primitiveSubstrate? substratePrimitive with
  | some object, some substrate =>
      objectSubstrateAllowedInBiome object substrate biome
  | _, _ => false

def spawnablePrimitiveNames : List PrimitiveShapeName :=
  primitiveShapeCatalog.filterMap
    (fun spec =>
      match primitiveObject? spec.name with
      | some _ => some spec.name
      | none => none)

def substratePrimitiveNames : List PrimitiveShapeName :=
  substratePrimitiveCatalog.map PrimitiveShapeSpec.name

def expectedSpawnablePrimitiveNames : List PrimitiveShapeName :=
  [ PrimitiveShapeName.oak
  , PrimitiveShapeName.pine
  , PrimitiveShapeName.maple
  , PrimitiveShapeName.willow
  , PrimitiveShapeName.birch
  , PrimitiveShapeName.cedar
  , PrimitiveShapeName.cypress
  , PrimitiveShapeName.palm
  , PrimitiveShapeName.baobab
  , PrimitiveShapeName.redwood
  , PrimitiveShapeName.spruce
  , PrimitiveShapeName.fir
  , PrimitiveShapeName.elm
  , PrimitiveShapeName.aspen
  , PrimitiveShapeName.fern
  , PrimitiveShapeName.boulder
  , PrimitiveShapeName.screeField
  , PrimitiveShapeName.sedimentLayer
  , PrimitiveShapeName.quartzPrism
  , PrimitiveShapeName.diamondOctahedron
  , PrimitiveShapeName.geode
  , PrimitiveShapeName.mountainRange
  , PrimitiveShapeName.ridge
  , PrimitiveShapeName.volcano
  , PrimitiveShapeName.plateau
  , PrimitiveShapeName.road
  , PrimitiveShapeName.serviceCenter
  , PrimitiveShapeName.human
  , PrimitiveShapeName.animal
  ]

theorem primitive_spawnable_catalog_certified :
    spawnablePrimitiveNames = expectedSpawnablePrimitiveNames /\
      substratePrimitiveNames =
        [ PrimitiveShapeName.soil
        , PrimitiveShapeName.forestFloor
        , PrimitiveShapeName.concrete
        , PrimitiveShapeName.asphalt
        , PrimitiveShapeName.bedrock
        , PrimitiveShapeName.alpinePeak
        , PrimitiveShapeName.water
        ] := by
  simp [spawnablePrimitiveNames, expectedSpawnablePrimitiveNames,
    substratePrimitiveNames, primitiveShapeCatalog, naturePrimitiveCatalog,
    botanicalPrimitiveCatalog, geologicPrimitiveCatalog,
    substratePrimitiveCatalog, civicPrimitiveCatalog, embodiedPrimitiveCatalog,
    primitiveShape, primitiveObject?]

theorem primitive_tree_cannot_spawn_on_alpine_peak :
    primitivePlacementAllowed PrimitiveShapeName.oak
      PrimitiveShapeName.alpinePeak Biome.alpine = false := by
  simp [primitivePlacementAllowed, primitiveObject?, primitiveSubstrate?,
    objectSubstrateAllowedInBiome, objectAllowedInBiome,
    substrateAllowedInBiome, placementAllowed]

theorem primitive_human_can_spawn_on_city_concrete :
    primitivePlacementAllowed PrimitiveShapeName.human
      PrimitiveShapeName.concrete Biome.city = true := by
  simp [primitivePlacementAllowed, primitiveObject?, primitiveSubstrate?,
    objectSubstrateAllowedInBiome, objectAllowedInBiome,
    substrateAllowedInBiome, placementAllowed]

theorem primitive_road_can_spawn_on_city_asphalt :
    primitivePlacementAllowed PrimitiveShapeName.road
      PrimitiveShapeName.asphalt Biome.city = true := by
  simp [primitivePlacementAllowed, primitiveObject?, primitiveSubstrate?,
    objectSubstrateAllowedInBiome, objectAllowedInBiome,
    substrateAllowedInBiome, placementAllowed]

theorem primitive_display_shape_is_not_spawnable_object :
    primitivePlacementAllowed PrimitiveShapeName.vortex
      PrimitiveShapeName.water Biome.coastal = false := by
  simp [primitivePlacementAllowed, primitiveObject?, primitiveSubstrate?]

/-! ## Spatial composition and cooperation -/

inductive CompanionRole where
  | thriller
  | spiller
  | filler
deriving DecidableEq, Repr

inductive SpatialComposition where
  | sameStratum
  | underCanopy
  | adjacentLattice
  | nestedLattice
deriving DecidableEq, Repr

inductive CooperationMode where
  | competition
  | mutualism
  | commensalism
  | neutral
deriving DecidableEq, Repr

inductive LocomotionClass where
  | aerial
  | terrestrial
  | rooted
  | inert
deriving DecidableEq, Repr

def companionRole? : PrimitiveShapeName -> Option CompanionRole
  | PrimitiveShapeName.oak => some CompanionRole.thriller
  | PrimitiveShapeName.pine => some CompanionRole.thriller
  | PrimitiveShapeName.maple => some CompanionRole.thriller
  | PrimitiveShapeName.willow => some CompanionRole.spiller
  | PrimitiveShapeName.birch => some CompanionRole.thriller
  | PrimitiveShapeName.cedar => some CompanionRole.thriller
  | PrimitiveShapeName.cypress => some CompanionRole.thriller
  | PrimitiveShapeName.palm => some CompanionRole.thriller
  | PrimitiveShapeName.baobab => some CompanionRole.thriller
  | PrimitiveShapeName.redwood => some CompanionRole.thriller
  | PrimitiveShapeName.spruce => some CompanionRole.thriller
  | PrimitiveShapeName.fir => some CompanionRole.thriller
  | PrimitiveShapeName.elm => some CompanionRole.thriller
  | PrimitiveShapeName.aspen => some CompanionRole.thriller
  | PrimitiveShapeName.fern => some CompanionRole.filler
  | _ => none

def bodyEnvelope : PrimitiveShapeName -> Nat
  | PrimitiveShapeName.oak => 4
  | PrimitiveShapeName.pine => 4
  | PrimitiveShapeName.maple => 4
  | PrimitiveShapeName.willow => 4
  | PrimitiveShapeName.birch => 3
  | PrimitiveShapeName.cedar => 4
  | PrimitiveShapeName.cypress => 3
  | PrimitiveShapeName.palm => 3
  | PrimitiveShapeName.baobab => 5
  | PrimitiveShapeName.redwood => 5
  | PrimitiveShapeName.spruce => 4
  | PrimitiveShapeName.fir => 4
  | PrimitiveShapeName.elm => 4
  | PrimitiveShapeName.aspen => 3
  | PrimitiveShapeName.fern => 1
  | PrimitiveShapeName.human => 2
  | PrimitiveShapeName.animal => 2
  | PrimitiveShapeName.boulder => 2
  | PrimitiveShapeName.screeField => 2
  | PrimitiveShapeName.sedimentLayer => 1
  | PrimitiveShapeName.quartzPrism => 1
  | PrimitiveShapeName.diamondOctahedron => 1
  | PrimitiveShapeName.geode => 1
  | PrimitiveShapeName.mountainRange => 5
  | PrimitiveShapeName.ridge => 3
  | PrimitiveShapeName.volcano => 4
  | PrimitiveShapeName.plateau => 4
  | PrimitiveShapeName.road => 1
  | PrimitiveShapeName.serviceCenter => 3
  | _ => 1

def rootspaceEnvelope : PrimitiveShapeName -> Nat
  | PrimitiveShapeName.oak => 4
  | PrimitiveShapeName.pine => 4
  | PrimitiveShapeName.maple => 4
  | PrimitiveShapeName.willow => 4
  | PrimitiveShapeName.birch => 3
  | PrimitiveShapeName.cedar => 4
  | PrimitiveShapeName.cypress => 3
  | PrimitiveShapeName.palm => 2
  | PrimitiveShapeName.baobab => 5
  | PrimitiveShapeName.redwood => 5
  | PrimitiveShapeName.spruce => 4
  | PrimitiveShapeName.fir => 4
  | PrimitiveShapeName.elm => 4
  | PrimitiveShapeName.aspen => 3
  | PrimitiveShapeName.fern => 1
  | PrimitiveShapeName.human => 2
  | PrimitiveShapeName.animal => 2
  | _ => 0

def locomotionClass : PrimitiveShapeName -> LocomotionClass
  | PrimitiveShapeName.human => LocomotionClass.terrestrial
  | PrimitiveShapeName.animal => LocomotionClass.terrestrial
  | PrimitiveShapeName.oak => LocomotionClass.rooted
  | PrimitiveShapeName.pine => LocomotionClass.rooted
  | PrimitiveShapeName.maple => LocomotionClass.rooted
  | PrimitiveShapeName.willow => LocomotionClass.rooted
  | PrimitiveShapeName.birch => LocomotionClass.rooted
  | PrimitiveShapeName.cedar => LocomotionClass.rooted
  | PrimitiveShapeName.cypress => LocomotionClass.rooted
  | PrimitiveShapeName.palm => LocomotionClass.rooted
  | PrimitiveShapeName.baobab => LocomotionClass.rooted
  | PrimitiveShapeName.redwood => LocomotionClass.rooted
  | PrimitiveShapeName.spruce => LocomotionClass.rooted
  | PrimitiveShapeName.fir => LocomotionClass.rooted
  | PrimitiveShapeName.elm => LocomotionClass.rooted
  | PrimitiveShapeName.aspen => LocomotionClass.rooted
  | PrimitiveShapeName.fern => LocomotionClass.rooted
  | _ => LocomotionClass.inert

def minimumSpacingFloor
    (left right : PrimitiveShapeName) : Nat :=
  max (bodyEnvelope left) (bodyEnvelope right)

def geometricSpacingSatisfied
    (left right : PrimitiveShapeName)
    (distance : Nat) : Bool :=
  minimumSpacingFloor left right <= distance

def cooperativeMode
    (composition : SpatialComposition)
    (sharedLattice : Bool)
    (mediaDemand mediaCapacity : Nat) : CooperationMode :=
  match composition with
  | SpatialComposition.sameStratum =>
      CooperationMode.competition
  | SpatialComposition.underCanopy =>
      if sharedLattice && mediaDemand <= mediaCapacity then
        CooperationMode.mutualism
      else
        CooperationMode.competition
  | SpatialComposition.adjacentLattice =>
      if sharedLattice && mediaDemand <= mediaCapacity then
        CooperationMode.commensalism
      else
        CooperationMode.neutral
  | SpatialComposition.nestedLattice =>
      if sharedLattice && mediaDemand <= mediaCapacity then
        CooperationMode.mutualism
      else
        CooperationMode.competition

def spatialCompositionAllowed
    (upper lower : PrimitiveShapeName)
    (composition : SpatialComposition)
    (distance : Nat)
    (sharedLattice : Bool)
    (mediaDemand mediaCapacity : Nat) : Bool :=
  match composition with
  | SpatialComposition.sameStratum =>
      geometricSpacingSatisfied upper lower distance
  | SpatialComposition.underCanopy =>
      sharedLattice && bodyEnvelope lower <= bodyEnvelope upper &&
        mediaDemand <= mediaCapacity
  | SpatialComposition.adjacentLattice =>
      sharedLattice && geometricSpacingSatisfied upper lower distance &&
        mediaDemand <= mediaCapacity
  | SpatialComposition.nestedLattice =>
      sharedLattice && bodyEnvelope lower <= bodyEnvelope upper &&
        mediaDemand <= mediaCapacity

def movementAllowedAcrossRootspace
    (agent occupiedBy : PrimitiveShapeName)
    (occupiedRootspace : Nat) : Bool :=
  match locomotionClass agent with
  | LocomotionClass.aerial => true
  | LocomotionClass.terrestrial =>
      occupiedRootspace = 0 || rootspaceEnvelope occupiedBy = 0
  | LocomotionClass.rooted => false
  | LocomotionClass.inert => false

def movementAllowedForLocomotion
    (agentClass : LocomotionClass)
    (occupiedBy : PrimitiveShapeName)
    (occupiedRootspace : Nat) : Bool :=
  match agentClass with
  | LocomotionClass.aerial => true
  | LocomotionClass.terrestrial =>
      occupiedRootspace = 0 || rootspaceEnvelope occupiedBy = 0
  | LocomotionClass.rooted => false
  | LocomotionClass.inert => false

theorem three_sisters_roles_certified :
    companionRole? PrimitiveShapeName.oak = some CompanionRole.thriller /\
      companionRole? PrimitiveShapeName.willow = some CompanionRole.spiller /\
      companionRole? PrimitiveShapeName.fern = some CompanionRole.filler := by
  simp [companionRole?]

theorem same_stratum_competition_requires_max_body_size :
    geometricSpacingSatisfied PrimitiveShapeName.oak PrimitiveShapeName.maple 3 = false /\
      geometricSpacingSatisfied PrimitiveShapeName.oak PrimitiveShapeName.maple 4 = true := by
  simp [geometricSpacingSatisfied, minimumSpacingFloor, bodyEnvelope]

theorem recursive_undergrowth_under_canopy_allowed :
    spatialCompositionAllowed PrimitiveShapeName.oak PrimitiveShapeName.fern
      SpatialComposition.underCanopy 0 true 2 3 = true /\
    cooperativeMode SpatialComposition.underCanopy true 2 3 =
      CooperationMode.mutualism := by
  simp [spatialCompositionAllowed, cooperativeMode, bodyEnvelope]

theorem recursive_undergrowth_blocks_energy_vacuum :
    spatialCompositionAllowed PrimitiveShapeName.oak PrimitiveShapeName.fern
      SpatialComposition.underCanopy 0 true 4 3 = false /\
    cooperativeMode SpatialComposition.underCanopy true 4 3 =
      CooperationMode.competition := by
  simp [spatialCompositionAllowed, cooperativeMode, bodyEnvelope]

theorem recursive_undergrowth_requires_shared_lattice :
    spatialCompositionAllowed PrimitiveShapeName.oak PrimitiveShapeName.fern
      SpatialComposition.underCanopy 0 false 1 3 = false := by
  simp [spatialCompositionAllowed, bodyEnvelope]

theorem humans_do_not_cross_filled_rootspace :
    movementAllowedAcrossRootspace PrimitiveShapeName.human
      PrimitiveShapeName.oak 1 = false := by
  simp [movementAllowedAcrossRootspace, locomotionClass, rootspaceEnvelope]

theorem humans_cross_unrooted_space :
    movementAllowedAcrossRootspace PrimitiveShapeName.human
      PrimitiveShapeName.road 1 = true := by
  simp [movementAllowedAcrossRootspace, locomotionClass, rootspaceEnvelope]

theorem aerial_agents_ignore_filled_rootspace :
    movementAllowedForLocomotion LocomotionClass.aerial
      PrimitiveShapeName.oak 1 = true := by
  simp [movementAllowedForLocomotion]

end Metaverse
end Gnosis
