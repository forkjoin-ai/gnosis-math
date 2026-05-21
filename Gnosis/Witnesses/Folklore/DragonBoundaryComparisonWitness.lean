import Gnosis.CadmusDragonTeethWitness
import Gnosis.GreekMonsterErrorPrimitivesWitness
import Gnosis.Witnesses.Chaldean.KarkartiamatDragonSeaMonsterWitness
import Gnosis.Witnesses.Chaldean.UddusunamirSphinxHadesGateWitness
import Gnosis.Witnesses.Chaldean.WiseManAirRiddleWitness
import Gnosis.Witnesses.Folklore.SaintGeorgeDragonTributeWitness

namespace Gnosis.Witnesses.Folklore
namespace DragonBoundaryComparisonWitness

/-!
# Dragon Boundary Comparison Witness

This module compares dragon carriers without collapsing them:

- Chaldean Karkartiamat: sea-chaos, fall vector, curse, and combat boundary.
- Cadmus: spring access wall and city-foundation seed compression.
- Greek monster atlas: boundary/error primitives.
- Saint George: civic tribute-loop rupture.
- Arthur/Pendragon: sovereignty mark, oath rotation, and hoard-collapse risk.
- Chaldean Sphinx/Uddusunamir: underworld gate repair and water-of-life release.
- Chaldean wise-man riddle: invisible air/wind carrier named by effects.

The shared topology is dragon-as-boundary-operator. The differences matter:
sea, spring, monster atlas, and tribute city expose different failure modes.

No `sorry`, no new `axiom`.
-/

structure DragonBoundaryInvariant where
  blocksOrTaxesAccess : Bool := true
  exposesCommunityFailureMode : Bool := true
  requiresBoundaryOperator : Bool := true
  testsAgentFitnessAtGate : Bool := true
  producesPostCombatOrdering : Bool := true
deriving DecidableEq, Repr

def dragonBoundaryInvariant : DragonBoundaryInvariant := {}

def sharedDragonBoundaryShape (d : DragonBoundaryInvariant) : Prop :=
  d.blocksOrTaxesAccess = true ∧
  d.exposesCommunityFailureMode = true ∧
  d.requiresBoundaryOperator = true ∧
  d.testsAgentFitnessAtGate = true ∧
  d.producesPostCombatOrdering = true

structure SourceDifferenceLedger where
  chaldeanSeaChaosPrimary : Bool := true
  cadmusSpringCityPrimary : Bool := true
  georgeTributeCityPrimary : Bool := true
  arthurSovereigntyTablePrimary : Bool := true
  chaldeanSphinxHadesGatePrimary : Bool := true
  chaldeanAirRiddlePrimary : Bool := true
  monsterAtlasErrorPrimitivePrimary : Bool := true
  noCarrierErasesAnother : Bool := true
deriving DecidableEq, Repr

def sourceDifferenceLedger : SourceDifferenceLedger := {}

def preservesDragonSourceDifferences (l : SourceDifferenceLedger) : Prop :=
  l.chaldeanSeaChaosPrimary = true ∧
  l.cadmusSpringCityPrimary = true ∧
  l.georgeTributeCityPrimary = true ∧
  l.arthurSovereigntyTablePrimary = true ∧
  l.chaldeanSphinxHadesGatePrimary = true ∧
  l.chaldeanAirRiddlePrimary = true ∧
  l.monsterAtlasErrorPrimitivePrimary = true ∧
  l.noCarrierErasesAnother = true

theorem dragon_boundary_shared_shape :
    sharedDragonBoundaryShape dragonBoundaryInvariant := by
  unfold sharedDragonBoundaryShape dragonBoundaryInvariant
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem dragon_boundary_preserves_source_differences :
    preservesDragonSourceDifferences sourceDifferenceLedger := by
  unfold preservesDragonSourceDifferences sourceDifferenceLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem dragon_boundary_cross_compare_witness :
    sharedDragonBoundaryShape dragonBoundaryInvariant ∧
    preservesDragonSourceDifferences sourceDifferenceLedger ∧
    Chaldean.KarkartiamatDragonSeaMonsterWitness.dragonActsAsBoundaryOperator
      Chaldean.KarkartiamatDragonSeaMonsterWitness.dragonBoundaryOperator ∧
    Gnosis.CadmusDragonTeethWitness.springAccessible
      Gnosis.CadmusDragonTeethWitness.dragonAtSpring = false ∧
    Gnosis.GreekMonsterErrorPrimitivesWitness.monsterBoundaryMarkers
      Gnosis.GreekMonsterErrorPrimitivesWitness.greekMonsterAtlas ∧
    Chaldean.UddusunamirSphinxHadesGateWitness.sphinxOpensUnderworldGate
      Chaldean.UddusunamirSphinxHadesGateWitness.uddusunamirSphinx ∧
    Chaldean.WiseManAirRiddleWitness.airWindSolvesRiddle
      Chaldean.WiseManAirRiddleWitness.airWindAnswer ∧
    SaintGeorgeDragonTributeWitness.tributeLoopBreaker
      SaintGeorgeDragonTributeWitness.saintlyIntervention := by
  exact ⟨dragon_boundary_shared_shape,
    dragon_boundary_preserves_source_differences,
    Chaldean.KarkartiamatDragonSeaMonsterWitness.karkartiamat_acts_as_boundary_operator,
    Gnosis.CadmusDragonTeethWitness.dragon_blocks_spring,
    Gnosis.GreekMonsterErrorPrimitivesWitness.monsters_mark_namespace_logic_gates,
    Chaldean.UddusunamirSphinxHadesGateWitness.uddusunamir_sphinx_opens_underworld_gate,
    Chaldean.WiseManAirRiddleWitness.wise_man_air_wind_solves_riddle,
    SaintGeorgeDragonTributeWitness.saint_george_breaks_tribute_loop⟩

end DragonBoundaryComparisonWitness
end Gnosis.Witnesses.Folklore
