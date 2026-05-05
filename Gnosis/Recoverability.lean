import Gnosis.VerifiedReconstruction

namespace Gnosis
namespace Recoverability

open LayeredNoise
open VerifiedReconstruction

/-!
# Recoverability

Recoverability is observer-relative. A signal is recoverable when it still
contains unresolved structure, but enough frame coverage and witness points
force a unique reconstruction.
-/

def recoverableAt (frame : ObserverFrame) (signal : HigherLayerSignal) : Prop :=
  partialObservation frame signal ∧
  ∃ problem : ReconstructionProblem,
    enoughFrames problem ∧
    hasPrimeKeystone problem ∧
    hasDoubleKeystone problem ∧
    ∃ valid : Fin problem.candidateCount → Prop, isUplifted problem valid

theorem canonical_pink_is_recoverable :
    recoverableAt aeonObserver pinkSaturationSignal := by
  refine ⟨pink_aeon_is_partial_observation, ?_⟩
  refine ⟨canonicalSieveProblem, canonical_problem_has_enough_frames, ?_⟩
  refine ⟨canonical_problem_has_prime_keystone, canonical_problem_has_double_keystone, ?_⟩
  refine ⟨fun c => c = ⟨0, by decide⟩, ?_⟩
  apply singleton_candidate_is_uplifted
  rfl

theorem coherence_needs_no_uplift
    (frame : ObserverFrame) (signal : HigherLayerSignal)
    (_hCoherent : coherentAt frame signal)
    (hRows : signal.saturationWitness ≤ frame.stableRows) :
    unresolvedResidue frame signal = 0 := by
  unfold unresolvedResidue
  exact Nat.sub_eq_zero_of_le hRows

theorem more_rows_help_recoverability
    (signal : HigherLayerSignal)
    {rows1 rows2 : Nat}
    (hRows : rows1 ≤ rows2)
    (hCap : rows2 ≤ signal.saturationWitness) :
    unresolvedResidue ⟨signal.complexity, rows2⟩ signal ≤
      unresolvedResidue ⟨signal.complexity, rows1⟩ signal := by
  exact more_stable_rows_reduce_residue signal hRows hCap

theorem brown_is_harder_than_pink_at_aeon :
    unresolvedResidue aeonObserver pinkSaturationSignal <
      unresolvedResidue aeonObserver brownSaturationSignal := by
  exact brown_exceeds_pink_residue_at_aeon

theorem zero_residue_blocks_partial_observation
    (frame : ObserverFrame) (signal : HigherLayerSignal)
    (hZero : unresolvedResidue frame signal = 0) :
    ¬ partialObservation frame signal := by
  unfold partialObservation
  rw [hZero]
  decide

end Recoverability
end Gnosis
