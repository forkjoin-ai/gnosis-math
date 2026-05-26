import Gnosis.MonsterJewelFanoUnfolding

/-
  MonsterJewelParticleSurvivor.lean
  =================================

  Particle Survivor theorem for the Monster jewel: each unfolded Fano/Plucker
  jewel cell is assigned a stable Phyle particle, and every assigned particle
  survives to the same time-bridge carrier.
-/

namespace GnosisMath
namespace MonsterJewelParticleSurvivor

open GnosisMath.MonsterJewelFanoUnfolding
open GnosisMath.TimeBridgeParticleShapeIsomorphism
open GnosisMath.TimeBridgeBigBangEmanation
open GnosisMath.TimeBridgePresentCarrier

/-- The stable particle assigned to one unfolded jewel cell. -/
def jewelCellParticle (_cell : JewelCell) : FoldedParticle :=
  stableParticleForShape ParticleShape.monsterJewel

/-- The full finite particle table used by the energized jewel. -/
def jewelSurvivorParticles : List FoldedParticle :=
  unfoldedJewelCells.map jewelCellParticle

theorem jewel_cell_particle_stable (cell : JewelCell) :
    mathematicallyStable defaultStabilityCutoff (jewelCellParticle cell) :=
  stable_shape_particle_is_stable ParticleShape.monsterJewel

theorem jewel_cell_particle_survives (cell : JewelCell) :
    survivorCarrier defaultStabilityCutoff (jewelCellParticle cell) =
      some (timeBridgePresent.entry, timeBridgePresent.exit) :=
  stable_particle_folds_onto_bridge defaultStabilityCutoff
    (jewelCellParticle cell) (jewel_cell_particle_stable cell)

theorem jewel_survivor_particles_length :
    jewelSurvivorParticles.length = 462 := by
  unfold jewelSurvivorParticles
  rw [List.length_map]
  exact unfolded_jewel_cells_length

theorem jewel_survivor_particles_stable
    (particle : FoldedParticle)
    (h : particle ∈ jewelSurvivorParticles) :
    mathematicallyStable defaultStabilityCutoff particle := by
  unfold jewelSurvivorParticles at h
  rcases List.mem_map.mp h with ⟨cell, _hcell, hparticle⟩
  rw [← hparticle]
  exact jewel_cell_particle_stable cell

theorem jewel_survivor_particles_survive
    (particle : FoldedParticle)
    (h : particle ∈ jewelSurvivorParticles) :
    survivorCarrier defaultStabilityCutoff particle =
      some (timeBridgePresent.entry, timeBridgePresent.exit) := by
  exact stable_particle_folds_onto_bridge defaultStabilityCutoff particle
    (jewel_survivor_particles_stable particle h)

/--
  Particle Survivor theorem: the energized Monster jewel has 462 finite
  particles, every particle is stable at the default Phyle cutoff, and every
  particle survives to the time-bridge carrier.
-/
theorem monster_jewel_particle_survivor_theorem :
    jewelSurvivorParticles.length = 462 ∧
    (∀ particle ∈ jewelSurvivorParticles,
      mathematicallyStable defaultStabilityCutoff particle) ∧
    (∀ particle ∈ jewelSurvivorParticles,
      survivorCarrier defaultStabilityCutoff particle =
        some (timeBridgePresent.entry, timeBridgePresent.exit)) :=
  ⟨jewel_survivor_particles_length,
   jewel_survivor_particles_stable,
   jewel_survivor_particles_survive⟩

end MonsterJewelParticleSurvivor
end GnosisMath
