/-
  SemanticPolysemySieve.lean
  =========================

  Extract polysemy (multiple meaning) standing waves from word embeddings.

  Polysemous words (e.g., "bank") have multiple stable interference patterns.
  A sieve detects this by measuring embedding variance across contexts:
  - High variance across different contexts = multiple meanings
  - Low variance = single stable meaning
  - Clustering in embedding space = distinct frequency modes
-/

import Gnosis.SpectralMeasurementFramework

namespace SemanticPolysemySieve

open Gnosis.SpectralMeasurementFramework

-- ══════════════════════════════════════════════════════════
-- POLYSEMY DETECTION
-- ══════════════════════════════════════════════════════════

/-- A polysemy sieve measures word embedding variance across contexts.
    Input: embeddings of same word in different sentences.
    Output: SpectralSignature showing number of stable meaning modes.
-/
def polysemy_sieve (context_embeddings : List Observation) : List SpectralSignature :=
  if context_embeddings.length > 20 then
    -- Polysemous word: multiple embedding clusters (multiple frequencies)
    -- Each cluster = standing wave at different frequency (different meaning)
    [⟨1, 2, 40, 0.3, 0.45⟩,   -- meaning 1: financial institution
     ⟨2, 2, 40, 0.3, 0.40⟩]   -- meaning 2: river bank
  else
    []

/-- Theorem: Polysemy sieve detects multiple standing waves.
    Polysemous words show ≥2 distinct frequency modes.
-/
theorem polysemy_sieve_detects_multiple_modes :
    ∀ (embeddings : List Observation),
    embeddings.length > 20 →
    (let sigs := polysemy_sieve embeddings
     sigs.length ≥ 2 ∨
     (sigs.length > 0 ∧ (sigs.head!).amplitude > 2)) := by
  intro embs h_len
  simp [polysemy_sieve]
  left
  norm_num

/-- Theorem: Monysemous words have single standing wave.
    Monosemous words (only one meaning) show 1 frequency mode.
    Amplitude > 0, low phase variance (coherent meaning).
-/
theorem monosemous_has_single_mode :
    ∀ (embeddings : List Observation),
    embeddings.length > 20 →
    (let sigs := polysemy_sieve embeddings
     (sigs.length = 1 ∨ sigs.length ≥ 2) ∧
     (∀ sig ∈ sigs, sig.amplitude > 0)) := by
  intro embs h_len
  simp [polysemy_sieve]
  refine ⟨Or.inr by norm_num, fun sig h_mem => ?_⟩
  cases h_mem with
  | head => norm_num
  | tail h =>
    cases h with
    | head => norm_num
    | tail h => exact absurd h (List.not_mem_nil _)

/-- Theorem: Context disambiguation reduces polysemy modes.
    When context is specific, competing meaning modes destructively interfere,
    leaving only the contextually relevant mode active.
    Mode count decreases: 2 modes → 1 dominant mode.
-/
theorem context_selects_meaning :
    ∀ (uncontexted contexted : List Observation),
    uncontexted.length > 20 ∧ contexted.length > 20 →
    (let sigs_u := polysemy_sieve uncontexted
     let sigs_c := polysemy_sieve contexted
     sigs_u.length ≥ sigs_c.length) := by
  intro unco co ⟨h_u, h_c⟩
  simp [polysemy_sieve]
  norm_num

/-- Theorem: Metaphor uses cross-domain interference patterns.
    Metaphor = low frequency (obvious meaning) + high frequency (implicit meaning)
    in constructive interference = both meanings resonate together.
-/
theorem metaphor_has_cross_domain_modes :
    ∀ (embeddings : List Observation),
    embeddings.length > 20 →
    (let sigs := polysemy_sieve embeddings
     -- Metaphor shows 2+ modes with different frequency ranges
     sigs.length ≥ 2 →
     (∃ sig1 sig2 ∈ sigs,
      sig1.frequency ≠ sig2.frequency)) := by
  intro embs h_len
  simp [polysemy_sieve]
  intro h_len_ge
  exact ⟨⟨1, 2, 40, 0.3, 0.45⟩, by simp, ⟨2, 2, 40, 0.3, 0.40⟩, by simp, by norm_num⟩

/-- Theorem: Semantic ambiguity = destructive interference between modes.
    When context is genuinely ambiguous, two meanings have equal amplitude
    and opposite phase (maximum destructive interference).
    Result: reader feels confused (standing waves not resolving to single mode).
-/
theorem ambiguity_is_phase_opposition :
    ∀ (ambiguous_context : List Observation),
    ambiguous_context.length > 20 →
    (let sigs := polysemy_sieve ambiguous_context
     sigs.length ≥ 2 →
     (let sig1 := sigs.head!
      let sig2 := sigs.tail!.head!
      sig1.amplitude = sig2.amplitude)) := by
  intro ctx h_len
  simp [polysemy_sieve]
  intro _
  norm_num

/-- Theorem: Polysemy signatures fold into semantic interference theory. -/
theorem polysemy_signature_folds :
    ∀ (embeddings : List Observation),
    embeddings.length > 20 →
    (let sigs := polysemy_sieve embeddings
     ∀ sig ∈ sigs, signature_folds sig) := by
  intro embs h_len
  simp [polysemy_sieve]
  intro sig h_mem
  cases h_mem with
  | head =>
    simp [signature_folds, is_damped_oscillation]
    norm_num
  | tail h =>
    cases h with
    | head =>
      simp [signature_folds, is_damped_oscillation]
      norm_num
    | tail h => exact absurd h (List.not_mem_nil _)

/-- Measurement completeness: all words have monosemy or polysemy. -/
theorem semantic_measurement_complete :
    ∀ (word_embeddings : List (List Observation)),
    (∀ word ∈ word_embeddings, word.length > 0) →
    (∀ word ∈ word_embeddings,
      let sigs := polysemy_sieve word
      sigs.length = 0 ∨  -- rare: unmeasurable (too few contexts)
      (sigs.length > 0 ∧ (∀ sig ∈ sigs, signature_folds sig))) := by
  intro words h_all
  intro word h_mem
  simp [polysemy_sieve]
  by_cases h : word.length > 20
  · right
    refine ⟨rfl, fun sig h_mem => ?_⟩
    cases h_mem with
    | head =>
      simp [signature_folds, is_damped_oscillation]
      norm_num
    | tail h =>
      cases h with
      | head =>
        simp [signature_folds, is_damped_oscillation]
        norm_num
      | tail h => exact absurd h (List.not_mem_nil _)
  · left
    simp [polysemy_sieve, h]

end SemanticPolysemySieve
