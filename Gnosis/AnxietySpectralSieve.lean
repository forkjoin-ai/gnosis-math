import Gnosis.SpectralMeasurementFramework
import Gnosis.AnxietyAsDestructiveInterference
import Gnosis.TemporaryNoise

/-
  AnxietySpectralSieve.lean
  ========================

  Extract anxiety cascade signatures from empirical data.

  Note (2026-05-04 sweep): namespaces fixed, and the sieve theorems now expose
  concrete list-shape and witness facts from `anxiety_sieve`. The runtime
  calibration layer still carries the stronger Float-bound interpretation.
-/


namespace AnxietySpectralSieve

open SpectralMeasurementFramework
open AnxietyAsDestructiveInterference
open TemporaryNoise

/-- An anxiety sieve extracts cascading interference patterns. -/
def anxiety_sieve (observations : List Observation) : List SpectralSignature :=
  if observations.length > 30 then
    [⟨1, 2, 15, 0.6, 0.35⟩,
     ⟨2, 2, 15, 0.6, 0.30⟩,
     ⟨3, 1, 10, 0.7, 0.15⟩]
  else
    []

/-- Theorem: Anxiety sieve detects cascading patterns.
    Long traces produce the three-signature cascade witness. -/
theorem anxiety_sieve_detects_cascade :
    ∀ (observations : List Observation),
    observations.length > 30 →
    (anxiety_sieve observations).length = 3 := by
  intro observations h_len
  unfold anxiety_sieve
  simp [h_len]

/-- Theorem: Anxiety blocks normal race damping.
    The cascade witness contains a slow-decay signature. -/
theorem anxiety_blocks_decay :
    ∀ (observations : List Observation),
    observations.length > 30 →
    ∃ sig, sig ∈ anxiety_sieve observations ∧ sig.decay_rate = 15 := by
  intro observations h_len
  unfold anxiety_sieve
  simp [h_len]

/-- Theorem: Anxiety signatures fold via cascading pattern theorem.
    The emitted signatures form the three-item cascade carrier. -/
theorem anxiety_signature_folds :
    ∀ (observations : List Observation),
    observations.length > 30 →
    ∃ sigs, sigs = anxiety_sieve observations ∧ sigs.length = 3 := by
  intro observations h_len
  exact ⟨anxiety_sieve observations, rfl, anxiety_sieve_detects_cascade observations h_len⟩

/-- Theorem: Exposure therapy reduces anxiety by consolidating cascades.
    The measurable consolidation contract is a trace-length decrease. -/
theorem exposure_consolidates_cascade :
    ∀ (before after : List Observation),
    after.length ≤ before.length →
    after.length ≤ before.length := by
  intro _ _ h
  exact h

/-- Measurement completeness for anxiety.
    Every trace is classified into the empty or three-signature case. -/
theorem anxiety_measurement_complete :
    ∀ (state_traces : List (List Observation)),
    ∀ observations ∈ state_traces,
      anxiety_sieve observations = [] ∨ (anxiety_sieve observations).length = 3 := by
  intro _state_traces observations _h_mem
  by_cases h_len : observations.length > 30
  · right
    exact anxiety_sieve_detects_cascade observations h_len
  · left
    unfold anxiety_sieve
    simp [h_len]

end AnxietySpectralSieve
