import Gnosis.CountBadLucasPhaseReconstruction

/-!
# Interference Residue Sequence

This module formalizes the finite, kernel-checked version of the
Lucas/Fibonacci leftover intuition:

* an observed integer recurrence can be compared against a Lucas carrier;
* the leftover is a signed residue, not discarded noise;
* in the `traceSeq` vs Lucas window reconstructed by
  `CountBadLucasPhaseReconstruction`, that residue is the balanced
  three-phase sequence `(+2, -1, -1)`;
* the phase has zero net drift over each full three-step overlap.

No global closed form is claimed here. The live witness is the same finite
window `n = 3 .. 12` already reconstructed in the Lucas phase module.
`Init` only through the imported module; no `sorry`, no new `axiom`.
-/

namespace Gnosis
namespace InterferenceResidueSequence

open CountBadLucasPhaseReconstruction

/-! ## Generic residue carrier -/

/-- Signed leftover between an observed integer sequence and a chosen basis. -/
def interferenceResidue (observed basis : Nat → Int) (n : Nat) : Int :=
  observed n - basis n

/-- `traceSeq` as an `Int`-valued observed recurrence. -/
def observedTrace (n : Nat) : Int :=
  (traceSeq n : Int)

/-- Lucas as the comparison carrier. -/
def lucasCarrier (n : Nat) : Int :=
  (lucas n : Int)

/-- Local Fibonacci carrier for the golden-discriminant overlap witness. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

/-- The actual signed leftover between `traceSeq` and Lucas. -/
def traceLucasResidue (n : Nat) : Int :=
  interferenceResidue observedTrace lucasCarrier n

/-! ## Three-phase interference model -/

/-- The proposed balanced residue pattern: crest at `3 ∣ n`, trough otherwise. -/
def goldenInterferenceResidue (n : Nat) : Int :=
  if n % 3 = 0 then 2 else -1

/-- One full phase cycle has zero net drift. -/
theorem golden_phase_cycle_zero :
    goldenInterferenceResidue 3 +
      goldenInterferenceResidue 4 +
      goldenInterferenceResidue 5 = 0 := by
  decide

/-- The next full phase cycle has the same zero-drift balance. -/
theorem golden_phase_cycle_zero_next :
    goldenInterferenceResidue 6 +
      goldenInterferenceResidue 7 +
      goldenInterferenceResidue 8 = 0 := by
  decide

/-- Every three-step overlap in the reconstructed window is balanced. -/
theorem golden_phase_window_balanced :
    ∀ n : Fin 8,
      let k := n.val + 3
      goldenInterferenceResidue k +
          goldenInterferenceResidue (k + 1) +
          goldenInterferenceResidue (k + 2) = 0 := by
  decide

/-! ## Fit against the reconstructed Lucas leftover -/

/-- The actual `traceSeq - Lucas` leftover equals the proposed phase model
through the reconstructed window `3 .. 12`. -/
theorem trace_lucas_residue_matches_golden_window :
    ∀ n : Fin 10,
      let k := n.val + 3
      traceLucasResidue k = goldenInterferenceResidue k := by
  decide

/-- Equivalent carrier decomposition over the reconstructed window. -/
theorem trace_decomposes_as_lucas_plus_golden_residue :
    ∀ n : Fin 10,
      let k := n.val + 3
      observedTrace k = lucasCarrier k + goldenInterferenceResidue k := by
  decide

/-- Constructive crest witnesses: at multiples of three, the leftover is `+2`. -/
theorem constructive_crests :
    traceLucasResidue 3 = 2 ∧
      traceLucasResidue 6 = 2 ∧
      traceLucasResidue 9 = 2 ∧
      traceLucasResidue 12 = 2 := by
  decide

/-- Destructive trough witnesses: away from multiples of three, the leftover is `-1`. -/
theorem destructive_troughs :
    traceLucasResidue 4 = -1 ∧
      traceLucasResidue 5 = -1 ∧
      traceLucasResidue 7 = -1 ∧
      traceLucasResidue 8 = -1 ∧
      traceLucasResidue 10 = -1 ∧
      traceLucasResidue 11 = -1 := by
  decide

/-- Packaged finite certificate: residue fit plus local zero-drift overlap. -/
theorem interference_residue_certificate :
    (∀ n : Fin 10,
      let k := n.val + 3
      traceLucasResidue k = goldenInterferenceResidue k)
    ∧
    (∀ n : Fin 8,
      let k := n.val + 3
      goldenInterferenceResidue k +
          goldenInterferenceResidue (k + 1) +
          goldenInterferenceResidue (k + 2) = 0)
    ∧
    traceLucasResidue 3 = 2
    ∧
    traceLucasResidue 4 = -1
    ∧
    traceLucasResidue 5 = -1 := by
  decide

/-! ## Golden discriminant overlap marker -/

/-- The discriminant constant remains the Lucas/Fibonacci square-gap marker. -/
def goldenDiscriminant : Nat := 5

/-- At `n = 5`, Lucas/Fibonacci overlap is governed by the golden
discriminant: `5 * F_5^2 = L_5^2 + 4`. -/
theorem golden_discriminant_overlap_at_five :
    goldenDiscriminant * (fib 5 * fib 5) = lucas 5 * lucas 5 + 4 := by
  decide

/-- The finite story in one theorem: the leftover is a balanced
three-phase interference residue, and the `5` overlap remains the
golden discriminant of the Lucas/Fibonacci carrier. -/
theorem balanced_leftover_with_golden_discriminant :
    (∀ n : Fin 10,
      let k := n.val + 3
      observedTrace k = lucasCarrier k + goldenInterferenceResidue k)
    ∧
    (∀ n : Fin 8,
      let k := n.val + 3
      goldenInterferenceResidue k +
          goldenInterferenceResidue (k + 1) +
          goldenInterferenceResidue (k + 2) = 0)
    ∧
    goldenDiscriminant * (fib 5 * fib 5) = lucas 5 * lucas 5 + 4 := by
  decide

end InterferenceResidueSequence
end Gnosis
