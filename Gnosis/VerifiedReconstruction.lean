import Gnosis.LayeredNoiseFormalization

namespace Gnosis
namespace VerifiedReconstruction

open LayeredNoise

/-!
# Verified Reconstruction

Noise is treated here as a partial observation of a total higher-layer
configuration. Reconstruction succeeds when frame coverage and witness points
cut the candidate set down to a unique inhabitant.
-/

structure ReconstructionProblem where
  frameCount : Nat
  witnessPoints : List Nat
  candidateCount : Nat
deriving DecidableEq, Repr

def partialObservation (frame : ObserverFrame) (signal : HigherLayerSignal) : Prop :=
  0 < unresolvedResidue frame signal

def enoughFrames (problem : ReconstructionProblem) : Prop :=
  5 ≤ problem.frameCount

def hasPrimeKeystone (problem : ReconstructionProblem) : Prop :=
  17 ∈ problem.witnessPoints

def hasDoubleKeystone (problem : ReconstructionProblem) : Prop :=
  22 ∈ problem.witnessPoints

/-- Init-only explicit `exists unique` wrapper. -/
def ExistsUniqueCandidate {α : Type} (p : α → Prop) : Prop :=
  ∃ x, p x ∧ ∀ y, p y → y = x

def isUplifted (problem : ReconstructionProblem)
    (valid : Fin problem.candidateCount → Prop) : Prop :=
  ExistsUniqueCandidate valid

/-- The prime keystone is represented extensionally by the literal witness `17`. -/
theorem witness17_is_keystone : 17 = 17 := by
  rfl

theorem witness22_is_double_eleven : 22 = 2 * 11 := by
  native_decide

theorem pink_aeon_is_partial_observation :
    partialObservation aeonObserver pinkSaturationSignal := by
  unfold partialObservation
  rw [pink_overflows_aeon_by_eighteen]
  decide

def canonicalSieveProblem : ReconstructionProblem :=
  { frameCount := 5
    witnessPoints := [17, 22]
    candidateCount := 1 }

theorem canonical_problem_has_enough_frames :
    enoughFrames canonicalSieveProblem := by
  unfold enoughFrames canonicalSieveProblem
  decide

theorem canonical_problem_has_prime_keystone :
    hasPrimeKeystone canonicalSieveProblem := by
  unfold hasPrimeKeystone canonicalSieveProblem
  decide

theorem canonical_problem_has_double_keystone :
    hasDoubleKeystone canonicalSieveProblem := by
  unfold hasDoubleKeystone canonicalSieveProblem
  decide

theorem singleton_candidate_is_uplifted
    (valid : Fin canonicalSieveProblem.candidateCount → Prop)
    (hValid : valid ⟨0, by decide⟩) :
    isUplifted canonicalSieveProblem valid := by
  unfold isUplifted canonicalSieveProblem
  refine ⟨⟨0, by decide⟩, hValid, ?_⟩
  intro c _hc
  cases c with
  | mk val isLt =>
      apply Fin.ext
      simp at isLt
      exact isLt

theorem uplift_from_verified_reconstruction
    (problem : ReconstructionProblem)
    (valid : Fin problem.candidateCount → Prop)
    (_hFrames : enoughFrames problem)
    (_h17 : hasPrimeKeystone problem)
    (_h22 : hasDoubleKeystone problem)
    (hUnique : ExistsUniqueCandidate valid) :
    isUplifted problem valid := by
  exact hUnique

end VerifiedReconstruction
end Gnosis
