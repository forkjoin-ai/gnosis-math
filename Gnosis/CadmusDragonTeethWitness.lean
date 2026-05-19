import Gnosis.SpectralNoiseEquilibrium

namespace Gnosis
namespace CadmusDragonTeethWitness

open SpectralNoiseEquilibrium

/-!
# Cadmus / Dragon's Teeth Witness

This module gives a first finite witness for Cadmus and the dragon's teeth.

Reading:

- The oracle and cow are formal pointers to a valid city coordinate.
- The dragon is an operational wall at the spring.
- The fallen companions record path divergence: a path that reaches the wall
  is falsified.
- The teeth are compressed seed tokens that fork into candidate agents.
- The Spartoi fight is adversarial filtering, leaving exactly five survivors.
- The five survivors are the fixed builder set for Thebes.
-/

/-- A small local atlas coordinate. -/
structure CityCoordinate where
  x : Nat
  y : Nat
deriving DecidableEq, Repr

def isValidCoordinate (coordinate : CityCoordinate) : Bool :=
  coordinate.x ≤ 3 && coordinate.y ≤ 3

def thebanCoordinate : CityCoordinate :=
  { x := 2, y := 1 }

/-- Oracle and cow signs both point at the same admissible city coordinate. -/
structure CityPointer where
  target : CityCoordinate
  validated : Bool
deriving DecidableEq, Repr

def oraclePointer : CityPointer :=
  { target := thebanCoordinate, validated := true }

def cowPointer : CityPointer :=
  { target := thebanCoordinate, validated := true }

def pointsToValidCity (pointer : CityPointer) : Prop :=
  pointer.validated = true ∧ isValidCoordinate pointer.target = true

theorem oracle_points_to_valid_city :
    pointsToValidCity oraclePointer := by
  exact ⟨rfl, rfl⟩

theorem cow_points_to_same_valid_city :
    pointsToValidCity cowPointer ∧ cowPointer.target = oraclePointer.target := by
  exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- The spring is accessible only when no operational wall guards it. -/
structure SpringAccess where
  coordinate : CityCoordinate
  wallPresent : Bool
deriving DecidableEq, Repr

def dragonAtSpring : SpringAccess :=
  { coordinate := thebanCoordinate, wallPresent := true }

def springAccessible (spring : SpringAccess) : Bool :=
  !spring.wallPresent

theorem dragon_blocks_spring :
    springAccessible dragonAtSpring = false := by
  rfl

/-- Companions are falsified when their path reaches the dragon wall. -/
structure CompanionPath where
  pathId : Nat
  reachesSpring : Bool
  crossesWall : Bool
deriving DecidableEq, Repr

def pathFalsified (path : CompanionPath) : Bool :=
  path.reachesSpring && path.crossesWall

def fallenCompanions : List CompanionPath :=
  [ { pathId := 0, reachesSpring := true, crossesWall := true }
  , { pathId := 1, reachesSpring := true, crossesWall := true }
  , { pathId := 2, reachesSpring := true, crossesWall := true }
  ]

theorem fallen_paths_are_divergent_falsifications :
    (fallenCompanions.map pathFalsified).all id = true := by
  rfl

/-- A tooth is a compressed seed: one token can fork into one candidate agent. -/
structure ToothSeed where
  seedId : Nat
  compressed : Bool
deriving DecidableEq, Repr

/-- One sown tooth carries the minimal Bule cost of a self-assembling seed. -/
def toothBuleSeed : BuleyUnit :=
  { waste := 1, opportunity := 0, diversity := 1 }

structure ForkedAgent where
  agentId : Nat
  fromSeed : Nat
  adversarialPass : Bool
  builderCapacity : Bool
deriving DecidableEq, Repr

def forkToAgent (seed : ToothSeed) : ForkedAgent :=
  { agentId := seed.seedId
    fromSeed := seed.seedId
    adversarialPass := seed.seedId < 5
    builderCapacity := seed.compressed }

def dragonTeeth : List ToothSeed :=
  [ { seedId := 0, compressed := true }
  , { seedId := 1, compressed := true }
  , { seedId := 2, compressed := true }
  , { seedId := 3, compressed := true }
  , { seedId := 4, compressed := true }
  , { seedId := 5, compressed := true }
  , { seedId := 6, compressed := true }
  ]

def spartoiCandidates : List ForkedAgent :=
  dragonTeeth.map forkToAgent

def passesSpartoiFilter (agent : ForkedAgent) : Bool :=
  agent.adversarialPass && agent.builderCapacity

def spartoiSurvivors : List ForkedAgent :=
  spartoiCandidates.filter passesSpartoiFilter

theorem teeth_fork_into_agents :
    spartoiCandidates.length = dragonTeeth.length := by
  rfl

theorem tooth_seed_has_positive_bule_cost :
    0 < buleyUnitScore toothBuleSeed := by
  unfold toothBuleSeed buleyUnitScore
  decide

theorem spartoi_filter_leaves_exactly_five :
    spartoiSurvivors.length = 5 := by
  rfl

theorem every_survivor_passes_filter :
    (spartoiSurvivors.map passesSpartoiFilter).all id = true := by
  rfl

/-- Thebes is stable when the valid coordinate is held by exactly five builders. -/
structure ThebesState where
  coordinate : CityCoordinate
  builderCount : Nat
  wallsRaised : Bool
deriving DecidableEq, Repr

def buildThebes (coordinate : CityCoordinate) (builders : List ForkedAgent) : ThebesState :=
  { coordinate := coordinate
    builderCount := builders.length
    wallsRaised := isValidCoordinate coordinate && builders.length == 5 }

def thebesFixedPoint : ThebesState :=
  buildThebes thebanCoordinate spartoiSurvivors

def isStableThebes (state : ThebesState) : Bool :=
  isValidCoordinate state.coordinate && state.wallsRaised && state.builderCount == 5

theorem survivors_build_stable_thebes :
    isStableThebes thebesFixedPoint = true := by
  rfl

theorem thebes_builders_are_fixed_point :
    buildThebes thebanCoordinate spartoiSurvivors = thebesFixedPoint := by
  rfl

/-- Master witness: pointer, wall, falsification, compression, adversarial
filtering, and fixed builders all compile into the Theban city state. -/
theorem cadmus_dragon_teeth_witness :
    pointsToValidCity oraclePointer ∧
    pointsToValidCity cowPointer ∧
    cowPointer.target = oraclePointer.target ∧
    springAccessible dragonAtSpring = false ∧
    (fallenCompanions.map pathFalsified).all id = true ∧
    0 < buleyUnitScore toothBuleSeed ∧
    spartoiCandidates.length = dragonTeeth.length ∧
    spartoiSurvivors.length = 5 ∧
    (spartoiSurvivors.map passesSpartoiFilter).all id = true ∧
    isStableThebes thebesFixedPoint = true ∧
    buildThebes thebanCoordinate spartoiSurvivors = thebesFixedPoint := by
  exact ⟨oracle_points_to_valid_city,
    cow_points_to_same_valid_city.left,
    cow_points_to_same_valid_city.right,
    dragon_blocks_spring,
    fallen_paths_are_divergent_falsifications,
    tooth_seed_has_positive_bule_cost,
    teeth_fork_into_agents,
    spartoi_filter_leaves_exactly_five,
    every_survivor_passes_filter,
    survivors_build_stable_thebes,
    thebes_builders_are_fixed_point⟩

end CadmusDragonTeethWitness
end Gnosis
