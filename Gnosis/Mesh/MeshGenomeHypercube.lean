import Init
import Gnosis.ArrowBuleDeficit


namespace Gnosis
namespace MeshGenomeHypercube

open ArrowBuleDeficit

inductive GenomeState
  | fitnessPeakFlow -- Convergent evolution
  | deleteriousDrift -- Random walk friction
  | geneticCollapse  -- Clonal decay / trap

inductive EvolutionaryForce
  | topologicalVacuum   -- Natural selection toward peaks
  | mutationalFriction  -- Genetic noise
  | pauliExclusion      -- Absolute fitness ceiling / extinction

def reduceGenomeState (s : GenomeState) : EvolutionaryForce :=
  match s with
  | GenomeState.fitnessPeakFlow => EvolutionaryForce.topologicalVacuum
  | GenomeState.deleteriousDrift => EvolutionaryForce.mutationalFriction
  | GenomeState.geneticCollapse => EvolutionaryForce.pauliExclusion

structure HypercubeKernel where
  mutationRate : Nat
  selectionPressure : Nat
  validGenome : mutationRate + selectionPressure > 0

def isFitnessTrapped (k : HypercubeKernel) : Prop :=
  k.mutationRate > k.selectionPressure

def applySexualRecombination (k : HypercubeKernel) (alpha : Nat) : HypercubeKernel :=
  { mutationRate := k.mutationRate
    selectionPressure := k.selectionPressure + alpha
    validGenome :=
      -- h : k.mutationRate + k.selectionPressure > 0
      -- Goal : k.mutationRate + (k.selectionPressure + alpha) > 0
      -- Rewrite to (k.mutationRate + k.selectionPressure) + alpha and bound.
      (Nat.add_assoc k.mutationRate k.selectionPressure alpha) ▸
        Nat.lt_of_lt_of_le k.validGenome
          (Nat.le_add_right (k.mutationRate + k.selectionPressure) alpha) }

theorem sex_restores_evolutionary_velocity (k : HypercubeKernel) :
    ∃ (alpha : Nat), ¬ isFitnessTrapped (applySexualRecombination k alpha) := by
  refine ⟨k.mutationRate, ?_⟩
  simp [isFitnessTrapped, applySexualRecombination]

end MeshGenomeHypercube
end Gnosis