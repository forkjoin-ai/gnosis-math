/-!
# Earth Tiling Topology

Finite earth-grid carrier inspired by `apps/storms-watch`: events snap to a
coarse lat/lon mesh, occupied cells become witnesses, and spawn propagation is
constrained to the tile and its four direct neighbors.
-/

namespace Gnosis
namespace EarthTilingTopology

structure EarthGrid where
  rows : Nat
  cols : Nat
  rowPos : 0 < rows
  colPos : 0 < cols

structure DegreeBounds where
  latMin : Int
  lonMin : Int
  step : Nat
  stepPos : 0 < step

def stormsWatchGrid : EarthGrid :=
  { rows := 34
    cols := 90
    rowPos := by decide
    colPos := by decide }

def stormsWatchBounds : DegreeBounds :=
  { latMin := -60
    lonMin := -180
    step := 4
    stepPos := by decide }

def tileCount (grid : EarthGrid) : Nat :=
  grid.rows * grid.cols

structure EarthTile (grid : EarthGrid) where
  row : Fin grid.rows
  col : Fin grid.cols
deriving DecidableEq, Repr

def tileIndex {grid : EarthGrid} (tile : EarthTile grid) : Nat :=
  tile.row.val * grid.cols + tile.col.val

def rowLatDegrees {grid : EarthGrid} (bounds : DegreeBounds) (tile : EarthTile grid) : Int :=
  bounds.latMin + Int.ofNat (bounds.step * tile.row.val)

def colLonDegrees {grid : EarthGrid} (bounds : DegreeBounds) (tile : EarthTile grid) : Int :=
  bounds.lonMin + Int.ofNat (bounds.step * tile.col.val)

structure TileCentroid where
  latDeg : Int
  lonDeg : Int
deriving DecidableEq, Repr

def tileCentroid {grid : EarthGrid} (bounds : DegreeBounds)
    (tile : EarthTile grid) : TileCentroid :=
  { latDeg := rowLatDegrees bounds tile
    lonDeg := colLonDegrees bounds tile }

def sameTile {grid : EarthGrid} (a b : EarthTile grid) : Prop :=
  a.row = b.row ∧ a.col = b.col

def north? {grid : EarthGrid} (tile : EarthTile grid) : Option (EarthTile grid) :=
  match tile.row with
  | ⟨0, _⟩ => none
  | ⟨row + 1, hrow⟩ =>
      some { row := ⟨row, Nat.lt_of_succ_lt hrow⟩, col := tile.col }

def south? {grid : EarthGrid} (tile : EarthTile grid) : Option (EarthTile grid) :=
  if h : tile.row.val + 1 < grid.rows then
    some { row := ⟨tile.row.val + 1, h⟩, col := tile.col }
  else
    none

def east {grid : EarthGrid} (tile : EarthTile grid) : EarthTile grid :=
  if h : tile.col.val + 1 < grid.cols then
    { row := tile.row, col := ⟨tile.col.val + 1, h⟩ }
  else
    { row := tile.row, col := ⟨0, grid.colPos⟩ }

def west {grid : EarthGrid} (tile : EarthTile grid) : EarthTile grid :=
  match tile.col with
  | ⟨0, _⟩ =>
      { row := tile.row
        col := ⟨grid.cols - 1, Nat.sub_one_lt_of_lt grid.colPos⟩ }
  | ⟨col + 1, hcol⟩ =>
      { row := tile.row, col := ⟨col, Nat.lt_of_succ_lt hcol⟩ }

inductive SpawnStep {grid : EarthGrid} : EarthTile grid → EarthTile grid → Prop where
  | stay (tile : EarthTile grid) : SpawnStep tile tile
  | north (tile next : EarthTile grid) :
      north? tile = some next → SpawnStep tile next
  | south (tile next : EarthTile grid) :
      south? tile = some next → SpawnStep tile next
  | east (tile : EarthTile grid) :
      SpawnStep tile (east tile)
  | west (tile : EarthTile grid) :
      SpawnStep tile (west tile)

structure MeshWitness (grid : EarthGrid) where
  tile : EarthTile grid
  intensity : Nat
  count : Nat

def occupied {grid : EarthGrid} (witness : MeshWitness grid) : Prop :=
  0 < witness.count

structure SpawnCertificate (grid : EarthGrid) where
  parent : MeshWitness grid
  child : MeshWitness grid
  step : SpawnStep parent.tile child.tile
  parentOccupied : occupied parent

def sampleTile : EarthTile stormsWatchGrid :=
  { row := ⟨12, by decide⟩
    col := ⟨45, by decide⟩ }

def antimeridianTile : EarthTile stormsWatchGrid :=
  { row := ⟨12, by decide⟩
    col := ⟨89, by decide⟩ }

def spawnedEastFromAntimeridian : EarthTile stormsWatchGrid :=
  east antimeridianTile

theorem storms_watch_tile_count :
    tileCount stormsWatchGrid = 3060 := by
  decide

theorem sample_tile_index :
    tileIndex sampleTile = 1125 := by
  decide

theorem sample_tile_centroid :
    tileCentroid stormsWatchBounds sampleTile = { latDeg := -12, lonDeg := 0 } := by
  decide

theorem antimeridian_east_wraps_to_zero_col :
    spawnedEastFromAntimeridian.col.val = 0 := by
  decide

theorem antimeridian_east_wraps_to_west_lon :
    (tileCentroid stormsWatchBounds spawnedEastFromAntimeridian).lonDeg = -180 := by
  decide

theorem sample_can_spawn_east :
    SpawnStep sampleTile (east sampleTile) :=
  SpawnStep.east sampleTile

theorem occupied_parent_can_certify_stay
    (parent : MeshWitness stormsWatchGrid) (h : occupied parent) :
    ∃ cert : SpawnCertificate stormsWatchGrid,
      cert.parent = parent ∧ cert.child.tile = parent.tile :=
  ⟨{ parent := parent,
      child := { tile := parent.tile, intensity := parent.intensity, count := parent.count },
      step := SpawnStep.stay parent.tile,
      parentOccupied := h },
    rfl,
    rfl⟩

end EarthTilingTopology
end Gnosis
