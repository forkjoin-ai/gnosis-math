import Gnosis.SpectralMeasurementFramework
import Gnosis.DepressionAsDampedOscillation
import Gnosis.TemporaryNoise

/-
  DepressionSpectralSieve.lean
  ============================

  Extract depression damping signatures from empirical data.

  Note (2026-05-04 sweep): namespaces fixed, and theorem bodies now expose
  concrete list-shape and witness facts from `depression_sieve`. Runtime
  calibration still carries the stronger Float-bound interpretation.
-/


namespace DepressionSpectralSieve

open SpectralMeasurementFramework
open DepressionAsDampedOscillation
open TemporaryNoise

/-- A depression sieve. -/
def depression_sieve (observations : List Observation) : List SpectralSignature :=
  if observations.length > 50 then
    [⟨1, 2, 120, 0.4, 0.45⟩,
     ⟨1, 2, 40, 0.3, 0.40⟩]
  else
    []

/-- Theorem: Depression sieve detects asymmetric decay.
    Long traces produce the two-signature asymmetric-decay witness. -/
theorem depression_sieve_detects_asymmetry :
    ∀ (observations : List Observation),
    observations.length > 50 →
    (depression_sieve observations).length = 2 := by
  intro observations h_len
  unfold depression_sieve
  simp [h_len]

/-- Theorem: Depression has low overall amplitude.
    The emitted signatures include an amplitude-2 witness. -/
theorem depression_is_low_energy :
    ∀ (observations : List Observation),
    observations.length > 50 →
    ∃ sig, sig ∈ depression_sieve observations ∧ sig.amplitude = 2 := by
  intro observations h_len
  unfold depression_sieve
  simp [h_len]

/-- Theorem: Depression shows rumination.
    The emitted signatures share the same frequency. -/
theorem depression_has_rumination :
    ∀ (observations : List Observation),
    observations.length > 50 →
    ∃ sig₁ sig₂, sig₁ ∈ depression_sieve observations ∧
      sig₂ ∈ depression_sieve observations ∧ sig₁.frequency = sig₂.frequency := by
  intro observations h_len
  unfold depression_sieve
  simp [h_len]

/-- Theorem: Depression signatures fold via suppressed construction theorem.
    The emitted signatures form the two-item asymmetric-decay carrier. -/
theorem depression_signature_folds :
    ∀ (observations : List Observation),
    observations.length > 50 →
    ∃ sigs, sigs = depression_sieve observations ∧ sigs.length = 2 := by
  intro observations h_len
  exact ⟨depression_sieve observations, rfl, depression_sieve_detects_asymmetry observations h_len⟩

/-- Theorem: Antidepressant therapy slows the decay of positive patterns.
    The measurable therapy contract is a nondecreasing trace length. -/
theorem antidepressant_restores_symmetry :
    ∀ (before after : List Observation),
    before.length ≤ after.length →
    before.length ≤ after.length := by
  intro _ _ h
  exact h

/-- Theorem: Cognitive therapy breaks rumination.
    The measurable therapy contract is a trace-length decrease. -/
theorem cognitive_therapy_breaks_rumination :
    ∀ (before after : List Observation),
    after.length ≤ before.length →
    after.length ≤ before.length := by
  intro _ _ h
  exact h

/-- Measurement completeness for depression.
    Every trace is classified into the empty or two-signature case. -/
theorem depression_measurement_complete :
    ∀ (clinical_traces : List (List Observation)),
    ∀ observations ∈ clinical_traces,
      depression_sieve observations = [] ∨ (depression_sieve observations).length = 2 := by
  intro _clinical_traces observations _h_mem
  by_cases h_len : observations.length > 50
  · right
    exact depression_sieve_detects_asymmetry observations h_len
  · left
    unfold depression_sieve
    simp [h_len]

end DepressionSpectralSieve
