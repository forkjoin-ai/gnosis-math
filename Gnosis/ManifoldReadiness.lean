import Gnosis.ObservabilityMetrics

namespace Gnosis
namespace ManifoldReadiness

open LayeredNoise
open VerifiedReconstruction
open Recoverability
open InformationAbsorption
open ObservabilityMetrics

/-!
# Manifold Readiness

Manifold readiness splits into two independent parts:

- carrier readiness: how much signal the substrate can hold locally,
- reconstruction readiness: how much witness structure is available to
  resolve what remains partial.
-/

def carrierReadiness (frame : ObserverFrame) (signal : HigherLayerSignal) : Int :=
  (absorbedInfo frame signal : Int) - (leakedInfo frame signal : Int)

def reconstructionReadiness (problem : ReconstructionProblem) : Int :=
  witnessScore problem

def manifoldReadiness (frame : ObserverFrame) (signal : HigherLayerSignal)
    (problem : ReconstructionProblem) : Int :=
  carrierReadiness frame signal + reconstructionReadiness problem

def carrierReady (frame : ObserverFrame) (signal : HigherLayerSignal) : Prop :=
  0 ≤ carrierReadiness frame signal

def readyForVerifiedUplift
    (frame : ObserverFrame) (signal : HigherLayerSignal)
    (problem : ReconstructionProblem) : Prop :=
  carrierReady frame signal ∧ recoverableAt frame signal ∧ 0 < reconstructionReadiness problem

theorem manifold_readiness_eq_observability
    (frame : ObserverFrame) (signal : HigherLayerSignal)
    (problem : ReconstructionProblem) :
    manifoldReadiness frame signal problem =
      observabilityScore frame signal problem := by
  unfold manifoldReadiness carrierReadiness reconstructionReadiness observabilityScore
  -- (absorbed - leaked) + witness = absorbed + witness - leaked
  rw [Int.sub_eq_add_neg, Int.add_right_comm]
  rfl

theorem canonical_reconstruction_readiness :
    reconstructionReadiness canonicalSieveProblem = 2 := by
  unfold reconstructionReadiness
  rw [canonical_problem_witness_score]
  rfl

theorem zero_leakage_carrier_readiness_is_absorption
    (frame : ObserverFrame) (signal : HigherLayerSignal)
    (hLeak : leakedInfo frame signal = 0) :
    carrierReadiness frame signal = absorbedInfo frame signal := by
  unfold carrierReadiness
  rw [hLeak]
  exact Int.sub_zero _

theorem carrier_readiness_linear_law
    (frame : ObserverFrame) (signal : HigherLayerSignal)
    (hOverflow : frame.stableRows ≤ signal.saturationWitness) :
    carrierReadiness frame signal =
      2 * (frame.stableRows : Int) - signal.saturationWitness := by
  unfold carrierReadiness absorbedInfo leakedInfo unresolvedResidue
  have h1 : signal.saturationWitness - (signal.saturationWitness - frame.stableRows) =
      frame.stableRows :=
    Nat.sub_sub_self hOverflow
  rw [h1, Int.ofNat_sub hOverflow]
  rw [Int.sub_eq_add_neg, Int.neg_sub, ← Int.add_sub_assoc, ← Int.two_mul]

theorem carrier_ready_iff_half_saturation
    (frame : ObserverFrame) (signal : HigherLayerSignal)
    (hOverflow : frame.stableRows ≤ signal.saturationWitness) :
    carrierReady frame signal ↔ signal.saturationWitness ≤ 2 * frame.stableRows := by
  unfold carrierReady
  rw [carrier_readiness_linear_law frame signal hOverflow]
  rw [Int.sub_nonneg]
  constructor
  · intro h
    have : ((signal.saturationWitness : Int)) ≤ ((2 * frame.stableRows : Nat) : Int) := by
      rw [Int.natCast_mul]; exact h
    exact Int.ofNat_le.mp this
  · intro h
    have : ((signal.saturationWitness : Int)) ≤ ((2 * frame.stableRows : Nat) : Int) :=
      Int.ofNat_le.mpr h
    rw [Int.natCast_mul] at this; exact this

theorem carrier_not_ready_iff_below_half_saturation
    (frame : ObserverFrame) (signal : HigherLayerSignal)
    (hOverflow : frame.stableRows ≤ signal.saturationWitness) :
    ¬ carrierReady frame signal ↔ 2 * frame.stableRows < signal.saturationWitness := by
  rw [carrier_ready_iff_half_saturation frame signal hOverflow]
  exact Nat.not_le

theorem zero_carrier_readiness_iff_exact_balance
    (frame : ObserverFrame) (signal : HigherLayerSignal)
    (hOverflow : frame.stableRows ≤ signal.saturationWitness) :
    carrierReadiness frame signal = 0 ↔
      signal.saturationWitness = 2 * frame.stableRows := by
  rw [carrier_readiness_linear_law frame signal hOverflow]
  rw [Int.sub_eq_zero]
  constructor
  · intro h
    have : ((signal.saturationWitness : Int)) = ((2 * frame.stableRows : Nat) : Int) := by
      rw [Int.natCast_mul]; exact h.symm
    exact Int.ofNat_inj.mp this
  · intro h
    have : ((signal.saturationWitness : Int)) = ((2 * frame.stableRows : Nat) : Int) :=
      Int.ofNat_inj.mpr h
    rw [Int.natCast_mul] at this; exact this.symm

theorem exact_balance_implies_carrier_ready
    (frame : ObserverFrame) (signal : HigherLayerSignal)
    (hOverflow : frame.stableRows ≤ signal.saturationWitness)
    (hBalance : signal.saturationWitness = 2 * frame.stableRows) :
    carrierReady frame signal := by
  rw [carrier_ready_iff_half_saturation frame signal hOverflow]
  exact Nat.le_of_eq hBalance

theorem exact_balance_is_vacuum_boundary
    (frame : ObserverFrame) (signal : HigherLayerSignal)
    (hOverflow : frame.stableRows ≤ signal.saturationWitness)
    (hBalance : signal.saturationWitness = 2 * frame.stableRows) :
    carrierReadiness frame signal = 0 := by
  rw [zero_carrier_readiness_iff_exact_balance frame signal hOverflow]
  exact hBalance

theorem each_extra_row_adds_two_readiness
    (signal : HigherLayerSignal) {r1 r2 : Nat}
    (hRows : r1 ≤ r2)
    (hOverflow : r2 ≤ signal.saturationWitness) :
    carrierReadiness ⟨signal.complexity, r2⟩ signal -
        carrierReadiness ⟨signal.complexity, r1⟩ signal =
      2 * ((r2 : Int) - r1) := by
  rw [carrier_readiness_linear_law ⟨signal.complexity, r2⟩ signal hOverflow,
    carrier_readiness_linear_law ⟨signal.complexity, r1⟩ signal (Nat.le_trans hRows hOverflow)]
  show (2 * (r2 : Int) + (-(signal.saturationWitness : Int)))
       - (2 * (r1 : Int) + (-(signal.saturationWitness : Int)))
       = 2 * ((r2 : Int) - r1)
  rw [Int.add_sub_add_right]
  exact (Int.mul_sub 2 (r2 : Int) (r1 : Int)).symm

theorem carrier_readiness_monotone_in_rows
    (signal : HigherLayerSignal) {r1 r2 : Nat}
    (hRows : r1 ≤ r2)
    (hOverflow : r2 ≤ signal.saturationWitness) :
    carrierReadiness ⟨signal.complexity, r1⟩ signal ≤
      carrierReadiness ⟨signal.complexity, r2⟩ signal := by
  rw [carrier_readiness_linear_law ⟨signal.complexity, r1⟩ signal (Nat.le_trans hRows hOverflow),
    carrier_readiness_linear_law ⟨signal.complexity, r2⟩ signal hOverflow]
  show 2 * (r1 : Int) - signal.saturationWitness ≤ 2 * (r2 : Int) - signal.saturationWitness
  exact Int.sub_le_sub_right
    (Int.mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr hRows) (by decide))
    _

theorem pink_aeon_carrier_readiness :
    carrierReadiness aeonObserver pinkSaturationSignal = -6 := by
  rw [carrier_readiness_linear_law aeonObserver pinkSaturationSignal]
  decide
  decide

theorem witness17_carrier_readiness_on_pink :
    carrierReadiness witness17Frame pinkSaturationSignal = 4 := by
  rw [carrier_readiness_linear_law witness17Frame pinkSaturationSignal]
  decide
  decide

theorem witness22_carrier_readiness_on_pink :
    carrierReadiness witness22Frame pinkSaturationSignal = 14 := by
  rw [carrier_readiness_linear_law witness22Frame pinkSaturationSignal]
  decide
  decide

theorem pink_aeon_is_not_carrier_ready :
    ¬ carrierReady aeonObserver pinkSaturationSignal := by
  unfold carrierReady
  rw [pink_aeon_carrier_readiness]
  decide

theorem pink_witness17_is_carrier_ready :
    carrierReady witness17Frame pinkSaturationSignal := by
  unfold carrierReady
  rw [witness17_carrier_readiness_on_pink]
  decide

theorem pink_witness22_is_carrier_ready :
    carrierReady witness22Frame pinkSaturationSignal := by
  unfold carrierReady
  rw [witness22_carrier_readiness_on_pink]
  decide

theorem recoverable_of_partial_with_canonical
    (frame : ObserverFrame) (signal : HigherLayerSignal)
    (hPartial : partialObservation frame signal) :
    recoverableAt frame signal := by
  refine ⟨hPartial, ?_⟩
  refine ⟨canonicalSieveProblem, canonical_problem_has_enough_frames, ?_⟩
  refine ⟨canonical_problem_has_prime_keystone, canonical_problem_has_double_keystone, ?_⟩
  refine ⟨fun c => c = ⟨0, by decide⟩, ?_⟩
  apply singleton_candidate_is_uplifted
  rfl

theorem pink_witness17_is_recoverable :
    recoverableAt witness17Frame pinkSaturationSignal := by
  apply recoverable_of_partial_with_canonical
  unfold partialObservation unresolvedResidue witness17Frame pinkSaturationSignal
  decide

theorem pink_witness22_is_recoverable :
    recoverableAt witness22Frame pinkSaturationSignal := by
  apply recoverable_of_partial_with_canonical
  unfold partialObservation unresolvedResidue witness22Frame pinkSaturationSignal
  decide

theorem pink_witness17_is_ready_for_verified_uplift :
    readyForVerifiedUplift witness17Frame pinkSaturationSignal canonicalSieveProblem := by
  refine ⟨pink_witness17_is_carrier_ready, pink_witness17_is_recoverable, ?_⟩
  unfold reconstructionReadiness
  rw [canonical_problem_witness_score]
  decide

theorem pink_witness22_is_ready_for_verified_uplift :
    readyForVerifiedUplift witness22Frame pinkSaturationSignal canonicalSieveProblem := by
  refine ⟨pink_witness22_is_carrier_ready, pink_witness22_is_recoverable, ?_⟩
  unfold reconstructionReadiness
  rw [canonical_problem_witness_score]
  decide

theorem brown_aeon_has_lower_carrier_readiness_than_pink :
    carrierReadiness aeonObserver brownSaturationSignal <
      carrierReadiness aeonObserver pinkSaturationSignal := by
  unfold carrierReadiness
  rw [pink_partial_absorption_at_aeon, pink_leakage_at_aeon, brown_leakage_at_aeon]
  unfold absorbedInfo unresolvedResidue aeonObserver brownSaturationSignal
  decide

end ManifoldReadiness
end Gnosis
