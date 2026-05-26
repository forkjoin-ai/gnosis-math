import Gnosis.MonsterAmplituhedronJewel

/-
  MonsterJewelFanoUnfolding.lean
  =================================

  Explicit table for the visual `j` scene: every one of the 66 unfolded
  Aeon/Plucker facets carries a seven-point Fano jewel. This gives the renderer
  a theorem-aligned finite index shape: 66 facets × 7 Fano points = 462 cells.
-/

namespace GnosisMath
namespace MonsterJewelFanoUnfolding

open GnosisMath.MonsterAmplituhedronJewel
open Gnosis.FanoFRFVI
open Gnosis.FanoIncidence
open Gnosis.ChromaticAeonMonsterResolution
open Gnosis.AeonCyclicPluckerLabels

/-- One rendered jewel cell: a Plucker facet index and a Fano root point. -/
structure JewelCell where
  facet : Fin jewelPluckerFacetCount
  point : FanoPoint
  deriving DecidableEq, Repr

/-- The seven visible Fano points in renderer order. -/
def jewelFanoPoints : List FanoPoint :=
  frfviCarrier.map toFanoPoint

/-- The 66 Plucker facets in renderer order. -/
def jewelFacetLabels : List (List Nat) :=
  pluckerTwoSubsetsAeon

/-- The full unfolded jewel table: every facet carries all seven Fano points. -/
def unfoldedJewelCells : List JewelCell :=
  (List.finRange jewelPluckerFacetCount).flatMap fun facet =>
    jewelFanoPoints.map fun point => { facet := facet, point := point }

theorem jewel_fano_points_length :
    jewelFanoPoints.length = 7 := by
  unfold jewelFanoPoints
  rw [List.length_map]
  exact frfvi_carrier_has_seven_points

theorem jewel_facet_labels_length :
    jewelFacetLabels.length = 66 := by
  unfold jewelFacetLabels
  exact pluckerTwoSubsetsAeon_length_sixty_six

theorem unfolded_jewel_cells_length :
    unfoldedJewelCells.length = 462 := by
  unfold unfoldedJewelCells jewelFanoPoints jewelPluckerFacetCount chromaticPairLabelCount
  native_decide

theorem unfolded_jewel_cells_length_factorized :
    unfoldedJewelCells.length =
      jewelPluckerFacetCount * jewelFanoRootCount := by
  rw [unfolded_jewel_cells_length, jewel_plucker_facet_count_closed,
    jewel_fano_root_count_closed]

theorem unfolded_jewel_facets_match_amplituhedron :
    jewelFacetLabels.length = jewelAmplituhedronVertexCount := by
  rw [jewel_facet_labels_length, jewel_amplituhedron_vertex_count_closed]

theorem unfolded_jewel_lands_below_monster_shell :
    unfoldedJewelCells.length < jewelMonsterShellCount := by
  rw [unfolded_jewel_cells_length, jewel_monster_shell_count_closed]
  decide

/--
  Bundle: the renderer table has 66 Plucker facets, seven Fano points on each
  facet, 462 cells total, the facet count matches the amplituhedron vertex
  carrier, and the full unfolded table remains below the Monster shell horizon.
-/
theorem monster_jewel_fano_unfolding_bundle :
    jewelFanoPoints.length = 7 ∧
    jewelFacetLabels.length = 66 ∧
    unfoldedJewelCells.length = 462 ∧
    unfoldedJewelCells.length =
      jewelPluckerFacetCount * jewelFanoRootCount ∧
    jewelFacetLabels.length = jewelAmplituhedronVertexCount ∧
    unfoldedJewelCells.length < jewelMonsterShellCount :=
  ⟨jewel_fano_points_length,
   jewel_facet_labels_length,
   unfolded_jewel_cells_length,
   unfolded_jewel_cells_length_factorized,
   unfolded_jewel_facets_match_amplituhedron,
   unfolded_jewel_lands_below_monster_shell⟩

end MonsterJewelFanoUnfolding
end GnosisMath
