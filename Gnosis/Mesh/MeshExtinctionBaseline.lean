import Init
import Gnosis.ArrowBuleDeficit


namespace Gnosis
namespace MeshExtinctionBaseline

open ArrowBuleDeficit

inductive BioState
  | speciationFlow    -- Adaptive radiation
  | environmentalStress -- Adaptation/Friction
  | massExtinction     -- Void / Depletion trap

inductive BioForce
  | topologicalVacuum   -- Diversity expansion
  | selectiveFriction   -- Evolutionary pressure
  | pauliExclusion      -- Absolute extinction / carrying capacity limit

def reduceBioState (s : BioState) : BioForce :=
  match s with
  | BioState.speciationFlow => BioForce.topologicalVacuum
  | BioState.environmentalStress => BioForce.selectiveFriction
  | BioState.massExtinction => BioForce.pauliExclusion

theorem extinction_is_exclusion : reduceBioState BioState.massExtinction = BioForce.pauliExclusion := rfl

structure ExtinctionKernel where
  stressLevel : Nat
  adaptiveRadiation : Nat
  validBiosphere : stressLevel + adaptiveRadiation > 0

def isBiosphereCollapsing (k : ExtinctionKernel) : Prop :=
  k.stressLevel > k.adaptiveRadiation

def applyNewSpeciation (k : ExtinctionKernel) (alpha : Nat) : ExtinctionKernel :=
  { stressLevel := k.stressLevel
    adaptiveRadiation := k.adaptiveRadiation + alpha
    validBiosphere := by
      have h : 0 < k.stressLevel + k.adaptiveRadiation := k.validBiosphere
      have h' : 0 < (k.stressLevel + k.adaptiveRadiation) + alpha :=
        Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h' }

theorem radiation_restores_equilibrium (k : ExtinctionKernel) :
    ∃ (alpha : Nat), ¬ isBiosphereCollapsing (applyNewSpeciation k alpha) := by
  refine ⟨k.stressLevel, ?_⟩
  simp [isBiosphereCollapsing, applyNewSpeciation]

end MeshExtinctionBaseline
end Gnosis
