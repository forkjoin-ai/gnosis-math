import Gnosis.PhyleContinuousManifoldClosure
import Gnosis.FanoFRFVI
import Gnosis.ChromaticAeonMonsterResolution
import Gnosis.AmplituhedronVertices

/-
  MonsterAmplituhedronJewel.lean
  =================================

  The unfolded jewel target for the next visual: Fano 7 supplies the visible
  root carrier, the Aeon/Plucker layer unfolds it to 66 pair labels, and the
  Monster shell supplies the 196884-side finite address horizon. The particle
  presentation remains Phyle/time-bridge encodable at finite resolution.
-/

namespace GnosisMath
namespace MonsterAmplituhedronJewel

open Gnosis.FanoFRFVI
open Gnosis.FanoIncidence
open Gnosis.ChromaticAeonMonsterResolution
open Gnosis.PleromaAeonMonsterBridge
open GnosisMath.TimeBridgeParticleShapeIsomorphism
open GnosisMath.TimeBridgeBigBangEmanation
open GnosisMath.TimeBridgePresentCarrier

/-- The seven-point Fano root of the unfolded jewel. -/
def jewelFanoRootCount : Nat :=
  frfviCarrier.length

/-- The unfolded Aeon/Plucker jewel layer. -/
def jewelPluckerFacetCount : Nat :=
  chromaticPairLabelCount

/-- The Monster-side finite shell addressed by the jewel. -/
def jewelMonsterShellCount : Nat :=
  chromaticMonsterShellDimension

/-- The amplituhedron Gr(2,12) vertex count used by the jewel. -/
def jewelAmplituhedronVertexCount : Nat :=
  AmplituhedronAttention.Vertices.vertexCount 2
    Gnosis.AeonStandingWaveCoordinateBridge.ambientDim

theorem jewel_fano_root_count_closed :
    jewelFanoRootCount = 7 := by
  unfold jewelFanoRootCount
  exact frfvi_carrier_has_seven_points

theorem jewel_plucker_facet_count_closed :
    jewelPluckerFacetCount = 66 :=
  chromatic_pair_label_count_closed

theorem jewel_amplituhedron_vertex_count_closed :
    jewelAmplituhedronVertexCount = 66 := by
  unfold jewelAmplituhedronVertexCount
  exact Gnosis.AeonStandingWaveCoordinateBridge.vertexCount_2_ambientDim_eq_sixty_six

theorem jewel_monster_shell_count_closed :
    jewelMonsterShellCount = 196884 :=
  chromatic_monster_shell_closed

theorem jewel_fano_unfolds_below_plucker :
    jewelFanoRootCount < jewelPluckerFacetCount := by
  rw [jewel_fano_root_count_closed, jewel_plucker_facet_count_closed]
  decide

theorem jewel_plucker_embeds_below_monster :
    jewelPluckerFacetCount < jewelMonsterShellCount := by
  rw [jewel_plucker_facet_count_closed, jewel_monster_shell_count_closed]
  decide

theorem jewel_plucker_matches_amplituhedron :
    jewelPluckerFacetCount = jewelAmplituhedronVertexCount := by
  rw [jewel_plucker_facet_count_closed, jewel_amplituhedron_vertex_count_closed]

theorem monster_jewel_carrier_isomorphic_to_bridge :
    CarrierIsomorphic (shapeCarrier ParticleShape.monsterJewel)
      (timeBridgePresent.entry, timeBridgePresent.exit) :=
  monster_jewel_maps_to_bridge_carrier

/--
  Bundle: the jewel unfolds Fano 7 into the 66 Aeon/Plucker amplituhedron layer,
  embeds that finite layer below the 196884 Monster shell, and keeps the visual
  particle presentation on the same time-bridge carrier.
-/
theorem monster_amplituhedron_jewel_bundle :
    jewelFanoRootCount = 7 ∧
    jewelPluckerFacetCount = 66 ∧
    jewelAmplituhedronVertexCount = 66 ∧
    jewelMonsterShellCount = 196884 ∧
    jewelFanoRootCount < jewelPluckerFacetCount ∧
    jewelPluckerFacetCount = jewelAmplituhedronVertexCount ∧
    jewelPluckerFacetCount < jewelMonsterShellCount ∧
    CarrierIsomorphic (shapeCarrier ParticleShape.monsterJewel)
      (timeBridgePresent.entry, timeBridgePresent.exit) :=
  ⟨jewel_fano_root_count_closed,
   jewel_plucker_facet_count_closed,
   jewel_amplituhedron_vertex_count_closed,
   jewel_monster_shell_count_closed,
   jewel_fano_unfolds_below_plucker,
   jewel_plucker_matches_amplituhedron,
   jewel_plucker_embeds_below_monster,
   monster_jewel_carrier_isomorphic_to_bridge⟩

end MonsterAmplituhedronJewel
end GnosisMath
