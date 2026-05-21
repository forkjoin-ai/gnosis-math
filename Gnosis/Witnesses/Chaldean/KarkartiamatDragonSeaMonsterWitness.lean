import Gnosis.CadmusDragonTeethWitness
import Gnosis.GreekMonsterErrorPrimitivesWitness
import Gnosis.Witnesses.Chaldean.MummuTiamatuWaterChaosCarrierWitness
import Gnosis.Witnesses.Chaldean.TiamatBoundaryCombatWitness

namespace Gnosis.Witnesses.Chaldean
namespace KarkartiamatDragonSeaMonsterWitness

/-!
# Karkartiamat Dragon / Sea-Monster Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Chapter V,
dragon/serpent/fall/war passages.

The source gives a valuable dragon witness because it refuses a clean modern
category. Karkartiamat is glossed as dragon of the sea; the signs point through
scaly creature, serpent, fish, fabulous dragon, den, griffin-like composite
body, and creature of Tiamat. That ambiguity is not noise. It is the witness:
the dragon marks the place where water-chaos, knowledge boundary, fall, curse,
and combat touch the same runtime edge.

This file keeps the Chaldean carrier primary. Greek and later dragon stories
are bridges, not governors.

No `sorry`, no new `axiom`.
-/

structure DragonNameMorphology where
  karkartiamatNamedDragonOfSea : Bool := true
  scalyMonogramReadingPreserved : Bool := true
  serpentFishDragonAmbiguityPreserved : Bool := true
  dragonDenNamedUnderReserve : Bool := true
  griffinScaledWingedCompositeForm : Bool := true
deriving DecidableEq, Repr

def dragonNameMorphology : DragonNameMorphology := {}

def preservesDragonMorphology (d : DragonNameMorphology) : Prop :=
  d.karkartiamatNamedDragonOfSea = true ∧
  d.scalyMonogramReadingPreserved = true ∧
  d.serpentFishDragonAmbiguityPreserved = true ∧
  d.dragonDenNamedUnderReserve = true ∧
  d.griffinScaledWingedCompositeForm = true

structure DragonFallVector where
  creatureOfTiamat : Bool := true
  livingSeaChaosPrinciple : Bool := true
  linkedToKnowledgeTreeBoundary : Bool := true
  linkedToFallAndCurse : Bool := true
  humanAfflictionLedgerOpened : Bool := true
deriving DecidableEq, Repr

def dragonFallVector : DragonFallVector := {}

def seaDragonCarriesFallVector (d : DragonFallVector) : Prop :=
  d.creatureOfTiamat = true ∧
  d.livingSeaChaosPrinciple = true ∧
  d.linkedToKnowledgeTreeBoundary = true ∧
  d.linkedToFallAndCurse = true ∧
  d.humanAfflictionLedgerOpened = true

structure DragonBoundaryOperator where
  notDecorativeMonster : Bool := true
  knowledgeBoundaryBreached : Bool := true
  seaChaosCrossesIntoMoralRuntime : Bool := true
  fallWarBridgeKeptUnderReserve : Bool := true
  boundaryToolsRequired : Bool := true
deriving DecidableEq, Repr

def dragonBoundaryOperator : DragonBoundaryOperator := {}

def dragonActsAsBoundaryOperator (d : DragonBoundaryOperator) : Prop :=
  d.notDecorativeMonster = true ∧
  d.knowledgeBoundaryBreached = true ∧
  d.seaChaosCrossesIntoMoralRuntime = true ∧
  d.fallWarBridgeKeptUnderReserve = true ∧
  d.boundaryToolsRequired = true

structure CrossTraditionDragonBridge where
  chaldeanCarrierRemainsPrimary : Bool := true
  cadmusShowsDragonAsAccessWall : Bool := true
  greekMonsterAtlasShowsBoundaryLogic : Bool := true
  comparisonDoesNotFlattenSources : Bool := true
deriving DecidableEq, Repr

def crossTraditionDragonBridge : CrossTraditionDragonBridge := {}

def dragonBridgeDiscipline (b : CrossTraditionDragonBridge) : Prop :=
  b.chaldeanCarrierRemainsPrimary = true ∧
  b.cadmusShowsDragonAsAccessWall = true ∧
  b.greekMonsterAtlasShowsBoundaryLogic = true ∧
  b.comparisonDoesNotFlattenSources = true

theorem karkartiamat_preserves_dragon_morphology :
    preservesDragonMorphology dragonNameMorphology := by
  unfold preservesDragonMorphology dragonNameMorphology
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem karkartiamat_carries_fall_vector :
    seaDragonCarriesFallVector dragonFallVector := by
  unfold seaDragonCarriesFallVector dragonFallVector
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem karkartiamat_acts_as_boundary_operator :
    dragonActsAsBoundaryOperator dragonBoundaryOperator := by
  unfold dragonActsAsBoundaryOperator dragonBoundaryOperator
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem karkartiamat_inherits_tiamat_boundary_combat :
    TiamatBoundaryCombatWitness.tiamatDragonBoundary
      TiamatBoundaryCombatWitness.seaDragonBoundary ∧
    TiamatBoundaryCombatWitness.windContainmentProtocol
      TiamatBoundaryCombatWitness.windMouthContainment := by
  exact ⟨TiamatBoundaryCombatWitness.tiamat_dragon_boundary_witness,
    TiamatBoundaryCombatWitness.tiamat_wind_containment_protocol⟩

theorem karkartiamat_inherits_water_chaos_carrier :
    MummuTiamatuWaterChaosCarrierWitness.chaosReturnsAtBoundary
      MummuTiamatuWaterChaosCarrierWitness.tiamatBoundaryReturn ∧
    MummuTiamatuWaterChaosCarrierWitness.seaFriendFoeTaming
      MummuTiamatuWaterChaosCarrierWitness.seaTamingAmbivalence := by
  exact ⟨MummuTiamatuWaterChaosCarrierWitness.mummu_tiamatu_returns_at_boundary,
    MummuTiamatuWaterChaosCarrierWitness.mummu_tiamatu_sea_friend_foe_taming⟩

theorem karkartiamat_cross_tradition_bridge :
    dragonBridgeDiscipline crossTraditionDragonBridge ∧
    Gnosis.CadmusDragonTeethWitness.springAccessible
      Gnosis.CadmusDragonTeethWitness.dragonAtSpring = false ∧
    Gnosis.GreekMonsterErrorPrimitivesWitness.monsterBoundaryMarkers
      Gnosis.GreekMonsterErrorPrimitivesWitness.greekMonsterAtlas := by
  exact ⟨by
    unfold dragonBridgeDiscipline crossTraditionDragonBridge
    exact ⟨rfl, rfl, rfl, rfl⟩,
    Gnosis.CadmusDragonTeethWitness.dragon_blocks_spring,
    Gnosis.GreekMonsterErrorPrimitivesWitness.monsters_mark_namespace_logic_gates⟩

theorem karkartiamat_dragon_sea_monster_witness :
    preservesDragonMorphology dragonNameMorphology ∧
    seaDragonCarriesFallVector dragonFallVector ∧
    dragonActsAsBoundaryOperator dragonBoundaryOperator ∧
    dragonBridgeDiscipline crossTraditionDragonBridge := by
  exact ⟨karkartiamat_preserves_dragon_morphology,
    karkartiamat_carries_fall_vector,
    karkartiamat_acts_as_boundary_operator,
    karkartiamat_cross_tradition_bridge.left⟩

end KarkartiamatDragonSeaMonsterWitness
end Gnosis.Witnesses.Chaldean
