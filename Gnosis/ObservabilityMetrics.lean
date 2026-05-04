import Gnosis.InformationAbsorption

namespace Gnosis
namespace ObservabilityMetrics

open LayeredNoise
open VerifiedReconstruction
open InformationAbsorption

/-!
# Observability Metrics

Measured noise predicts observability through three quantities:

- absorbed signal units,
- leaked signal units,
- witness/frame support for reconstruction.
-/

def witnessScore (problem : ReconstructionProblem) : Nat :=
  (if _h : 17 ∈ problem.witnessPoints then 1 else 0) +
  (if _h : 22 ∈ problem.witnessPoints then 1 else 0)

def observabilityScore (frame : ObserverFrame) (signal : HigherLayerSignal)
    (problem : ReconstructionProblem) : Int :=
  (absorbedInfo frame signal : Int) +
  (witnessScore problem : Int) -
  (leakedInfo frame signal : Int)

theorem canonical_problem_witness_score :
    witnessScore canonicalSieveProblem = 2 := by
  unfold witnessScore
  native_decide

theorem pink_aeon_observability_score :
    observabilityScore aeonObserver pinkSaturationSignal canonicalSieveProblem =
      (Gnosis.Circadian.aeon : Int) + 2 - 18 := by
  unfold observabilityScore
  rw [pink_partial_absorption_at_aeon, canonical_problem_witness_score, pink_leakage_at_aeon]
  rfl

theorem more_rows_reduce_noise_pressure
    (signal : HigherLayerSignal) {r1 r2 : Nat}
    (hRows : r1 ≤ r2)
    (hCap : r2 ≤ signal.saturationWitness) :
    leakedInfo ⟨signal.complexity, r2⟩ signal ≤
      leakedInfo ⟨signal.complexity, r1⟩ signal := by
  exact more_stable_rows_reduce_residue signal hRows hCap

theorem witness17_improves_pink_observability :
    observabilityScore aeonObserver pinkSaturationSignal canonicalSieveProblem <
      observabilityScore witness17Frame pinkSaturationSignal canonicalSieveProblem := by
  unfold observabilityScore
  rw [canonical_problem_witness_score, pink_partial_absorption_at_aeon, pink_leakage_at_aeon]
  unfold absorbedInfo leakedInfo unresolvedResidue witness17Frame pinkSaturationSignal
  native_decide

theorem witness22_improves_pink_observability :
    observabilityScore witness17Frame pinkSaturationSignal canonicalSieveProblem <
      observabilityScore witness22Frame pinkSaturationSignal canonicalSieveProblem := by
  unfold observabilityScore
  rw [canonical_problem_witness_score]
  unfold absorbedInfo leakedInfo unresolvedResidue witness17Frame witness22Frame pinkSaturationSignal
  native_decide

theorem brown_is_less_observable_than_pink_at_aeon :
    observabilityScore aeonObserver brownSaturationSignal canonicalSieveProblem <
      observabilityScore aeonObserver pinkSaturationSignal canonicalSieveProblem := by
  unfold observabilityScore
  rw [canonical_problem_witness_score, pink_partial_absorption_at_aeon, pink_leakage_at_aeon,
    brown_leakage_at_aeon]
  unfold absorbedInfo unresolvedResidue aeonObserver brownSaturationSignal
  native_decide

theorem zero_leakage_maximizes_local_observability
    (frame : ObserverFrame) (signal : HigherLayerSignal)
    (problem : ReconstructionProblem)
    (hLeak : leakedInfo frame signal = 0) :
    observabilityScore frame signal problem =
      (absorbedInfo frame signal : Int) + witnessScore problem := by
  unfold observabilityScore
  rw [hLeak]
  -- After rewrite the goal is
  --   ↑(absorbedInfo frame signal) + ↑(witnessScore problem) - ↑(0 : Nat)
  --     = ↑(absorbedInfo frame signal) + ↑(witnessScore problem)
  -- ((0 : Nat) : Int) = 0 by `Int.ofNat_zero` (Init); then `Int.sub_zero`.
  rw [Int.ofNat_zero, Int.sub_zero]

end ObservabilityMetrics
end Gnosis
