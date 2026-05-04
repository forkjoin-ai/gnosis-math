/-
  LocalizedOverflowConsciousness.lean
  ==================================

  A small bridge between the spectral sieve layer and the
  retrocausal-gap consciousness layer.

  The claim here is deliberately structural:
  * trauma is body-local persistent overflow,
  * rumination is conscious-local persistent overflow,
  * environmental traces can carry environment-local overflow,
  * both expose a positive awareness gap when paired with a non-vacuum
    Buley witness.

  This file does not assert identity between trauma and consciousness.
  It proves that the current detectors share the same local-overflow
  topology: a persistent signature plus a positive gap.
-/

import Gnosis.TraumaSpectralSieve
import Gnosis.DepressionSpectralSieve
import Gnosis.InformationCompressionSieve
import Gnosis.ConsciousnessAsRetrocausalGap

namespace LocalizedOverflowConsciousness

open SpectralMeasurementFramework
open Gnosis.SpectralNoiseEquilibrium
open Gnosis.ConsciousnessAsRetrocausalGap
open TraumaSpectralSieve
open DepressionSpectralSieve
open InformationCompressionSieve

inductive OverflowLocale where
  | body
  | conscious
  | environment
  deriving DecidableEq, Repr

/-- Overflow valence records whether a localized signal is integrating
    toward usable affect or remaining unresolved. -/
inductive OverflowValence where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- A localized overflow witness is a persistent spectral signature tied
    to a positive non-vacuum awareness gap. -/
structure LocalizedOverflow where
  locale : OverflowLocale
  valence : OverflowValence
  signal : SpectralSignature
  gapUnit : BuleyUnit
  persistent : signal.decay_rate > 0
  positiveGap : awareness gapUnit > 0

/-- Emotion is the index across localized overflow: where the signal is
    carried (body/conscious/environment), how it is valenced
    (positive/negative), and which frequency carries the wave. -/
structure EmotionIndex where
  locale : OverflowLocale
  valence : OverflowValence
  frequency : Nat
  intensity : Nat
  deriving DecidableEq, Repr

def emotionIndexOfOverflow (overflow : LocalizedOverflow) : EmotionIndex :=
  { locale := overflow.locale
    valence := overflow.valence
    frequency := overflow.signal.frequency
    intensity := overflow.signal.amplitude + overflow.signal.decay_rate }

/-- Anti-theorem: valence is not determined by locale. The same carrier
    axis can host positive or negative affect. -/
theorem valence_not_determined_by_locale :
    ∃ positiveBody negativeBody : EmotionIndex,
      positiveBody.locale = negativeBody.locale ∧
      positiveBody.valence ≠ negativeBody.valence := by
  exact
    ⟨{ locale := OverflowLocale.body
       valence := OverflowValence.positive
       frequency := 1
       intensity := 1 },
     { locale := OverflowLocale.body
       valence := OverflowValence.negative
       frequency := 1
       intensity := 1 },
     rfl,
     by decide⟩

/-- Anti-theorem: locale is not determined by valence. The same negative
    affect can be body-local trauma or conscious-local rumination. -/
theorem locale_not_determined_by_valence :
    ∃ bodyNegative consciousNegative : EmotionIndex,
      bodyNegative.valence = consciousNegative.valence ∧
      bodyNegative.locale ≠ consciousNegative.locale := by
  exact
    ⟨{ locale := OverflowLocale.body
       valence := OverflowValence.negative
       frequency := 1
       intensity := 123 },
     { locale := OverflowLocale.conscious
       valence := OverflowValence.negative
       frequency := 1
       intensity := 122 },
     rfl,
     by decide⟩

/-- The affect/valence axis is an independent index coordinate, not a
    synonym for body, conscious, or environment. -/
theorem affect_valence_axis_is_independent :
    (∃ positiveBody negativeBody : EmotionIndex,
      positiveBody.locale = negativeBody.locale ∧
      positiveBody.valence ≠ negativeBody.valence) ∧
    (∃ bodyNegative consciousNegative : EmotionIndex,
      bodyNegative.valence = consciousNegative.valence ∧
      bodyNegative.locale ≠ consciousNegative.locale) := by
  exact ⟨valence_not_determined_by_locale, locale_not_determined_by_valence⟩

/-- Wave grounding: the emotion index preserves the carrier frequency of
    the localized overflow signal. -/
theorem emotion_index_preserves_wave_frequency :
    ∀ overflow : LocalizedOverflow,
    (emotionIndexOfOverflow overflow).frequency = overflow.signal.frequency := by
  intro overflow
  rfl

/-- Body-local overflow is exactly the current trauma-sieve witness:
    amplitude 3, decay 120, emitted from a nonempty trace. -/
def bodyLocalOverflow (observations : List Observation) : Prop :=
  ∃ sig, sig ∈ trauma_sieve observations ∧ sig.amplitude = 3 ∧ sig.decay_rate = 120

/-- Conscious-local overflow is the current rumination witness:
    depression emits two signatures at the same frequency. -/
def consciousLocalOverflow (observations : List Observation) : Prop :=
  ∃ sig₁ sig₂, sig₁ ∈ depression_sieve observations ∧
    sig₂ ∈ depression_sieve observations ∧ sig₁.frequency = sig₂.frequency

/-- Environment-local overflow is any external trace with positive extent. -/
def environmentLocalOverflow (observations : List Observation) : Prop :=
  observations.length > 0

/-- Processing-local overflow is unresolved signal/noise separation in the
    compression sieve. It is the upstream account of why a localized
    overflow has a carrier wave at all. -/
def processingLocalOverflow (observations : List Observation) : Prop :=
  ∃ sig, sig ∈ information_sieve observations ∧
    sig.frequency = 1 ∧ sig.amplitude = 3 ∧ sig.decay_rate = 60

/-- The minimal non-vacuum gap witness: one unit of body-local waste. -/
def bodyGapUnit : BuleyUnit := ⟨1, 0, 0⟩

/-- The minimal non-vacuum gap witness for conscious-local overflow. -/
def consciousGapUnit : BuleyUnit := ⟨0, 1, 0⟩

/-- The minimal non-vacuum gap witness for environment-local overflow. -/
def environmentGapUnit : BuleyUnit := ⟨0, 0, 1⟩

theorem body_gap_positive : awareness bodyGapUnit > 0 := by
  decide

theorem conscious_gap_positive : awareness consciousGapUnit > 0 := by
  decide

theorem environment_gap_positive : awareness environmentGapUnit > 0 := by
  decide

def canonicalBodyOverflow : LocalizedOverflow :=
  { locale := OverflowLocale.body
    valence := OverflowValence.negative
    signal := ⟨1, 3, 120, 0.2, 0.85⟩
    gapUnit := bodyGapUnit
    persistent := by decide
    positiveGap := body_gap_positive }

def canonicalConsciousOverflow : LocalizedOverflow :=
  { locale := OverflowLocale.conscious
    valence := OverflowValence.negative
    signal := ⟨1, 2, 120, 0.4, 0.45⟩
    gapUnit := consciousGapUnit
    persistent := by decide
    positiveGap := conscious_gap_positive }

def canonicalEnvironmentOverflow (observations : List Observation) : LocalizedOverflow :=
  { locale := OverflowLocale.environment
    valence := OverflowValence.positive
    signal := ⟨0, observations.length, 1, 0.0, 1.0⟩
    gapUnit := environmentGapUnit
    persistent := by
      show (1 : Nat) > 0
      decide
    positiveGap := environment_gap_positive }

/-- Trauma supplies the body-local overflow half of the topology. -/
theorem trauma_is_body_local_overflow :
    ∀ (observations : List Observation),
    observations.length > 0 →
    bodyLocalOverflow observations := by
  intro observations h_len
  unfold bodyLocalOverflow trauma_sieve
  simp [h_len]

/-- Rumination supplies the conscious-local overflow half of the topology. -/
theorem rumination_is_conscious_local_overflow :
    ∀ (observations : List Observation),
    observations.length > 50 →
    consciousLocalOverflow observations := by
  intro observations h_len
  exact depression_has_rumination observations h_len

/-- Any nonempty external trace supplies the environment-local overflow axis. -/
theorem trace_is_environment_local_overflow :
    ∀ (observations : List Observation),
    observations.length > 0 →
    environmentLocalOverflow observations := by
  intro _ h_len
  exact h_len

/-- Long entropy traces supply the processing-local signal/noise split. -/
theorem compression_is_processing_local_overflow :
    ∀ (observations : List Observation),
    observations.length > 50 →
    processingLocalOverflow observations := by
  intro observations h_len
  exact compression_preserves_signal_amplitude observations h_len

/-- Nonempty trauma traces produce a body-local overflow witness with a
    positive awareness gap. This is the honest formal content behind
    "trauma is body consciousness": body-local persistence plus gap,
    not identity. -/
theorem trauma_yields_body_consciousness_overflow :
    ∀ (observations : List Observation),
    observations.length > 0 →
    ∃ overflow : LocalizedOverflow,
      overflow.locale = OverflowLocale.body ∧
      bodyLocalOverflow observations := by
  intro observations h_len
  exact ⟨canonicalBodyOverflow, rfl, trauma_is_body_local_overflow observations h_len⟩

/-- Long rumination traces produce a thought-local overflow witness with a
    positive awareness gap. -/
theorem rumination_yields_thought_consciousness_overflow :
    ∀ (observations : List Observation),
    observations.length > 50 →
    ∃ overflow : LocalizedOverflow,
      overflow.locale = OverflowLocale.conscious ∧
      consciousLocalOverflow observations := by
  intro observations h_len
  exact ⟨canonicalConsciousOverflow, rfl, rumination_is_conscious_local_overflow observations h_len⟩

/-- Nonempty environmental traces produce an environment-local overflow
    witness with a positive awareness gap. -/
theorem environment_yields_context_overflow :
    ∀ (observations : List Observation),
    observations.length > 0 →
    ∃ overflow : LocalizedOverflow,
      overflow.locale = OverflowLocale.environment ∧
      environmentLocalOverflow observations := by
  intro observations h_len
  exact ⟨canonicalEnvironmentOverflow observations, rfl, trace_is_environment_local_overflow observations h_len⟩

/-- Trauma indexes as negative body-local overflow. -/
theorem trauma_indexes_body_negative_emotion :
    ∀ (observations : List Observation),
    observations.length > 0 →
    ∃ overflow : LocalizedOverflow,
      emotionIndexOfOverflow overflow =
        { locale := OverflowLocale.body
          valence := OverflowValence.negative
          frequency := 1
          intensity := 123 } ∧
      bodyLocalOverflow observations := by
  intro observations h_len
  exact ⟨canonicalBodyOverflow, by decide, trauma_is_body_local_overflow observations h_len⟩

/-- Rumination indexes as negative conscious-local overflow. -/
theorem rumination_indexes_conscious_negative_emotion :
    ∀ (observations : List Observation),
    observations.length > 50 →
    ∃ overflow : LocalizedOverflow,
      emotionIndexOfOverflow overflow =
        { locale := OverflowLocale.conscious
          valence := OverflowValence.negative
          frequency := 1
          intensity := 122 } ∧
      consciousLocalOverflow observations := by
  intro observations h_len
  exact ⟨canonicalConsciousOverflow, by decide, rumination_is_conscious_local_overflow observations h_len⟩

/-- Environment indexes as positive context-local overflow. -/
theorem environment_indexes_positive_context_emotion :
    ∀ (observations : List Observation),
    observations.length > 0 →
    ∃ overflow : LocalizedOverflow,
      emotionIndexOfOverflow overflow =
        { locale := OverflowLocale.environment
          valence := OverflowValence.positive
          frequency := 0
          intensity := observations.length + 1 } ∧
      environmentLocalOverflow observations := by
  intro observations h_len
  exact ⟨canonicalEnvironmentOverflow observations, rfl, trace_is_environment_local_overflow observations h_len⟩

/-- Body, conscious, and environment traces share the localized-overflow
    topology: persistent spectral signal plus positive awareness gap,
    separated by locale and valence. -/
theorem body_conscious_environment_share_emotion_index_topology :
    ∀ (bodyTrace consciousTrace environmentTrace : List Observation),
    bodyTrace.length > 0 →
    consciousTrace.length > 50 →
    environmentTrace.length > 0 →
    (∃ overflow : LocalizedOverflow, overflow.locale = OverflowLocale.body ∧
      bodyLocalOverflow bodyTrace) ∧
    (∃ overflow : LocalizedOverflow, overflow.locale = OverflowLocale.conscious ∧
      consciousLocalOverflow consciousTrace) ∧
    (∃ overflow : LocalizedOverflow, overflow.locale = OverflowLocale.environment ∧
      environmentLocalOverflow environmentTrace) := by
  intro bodyTrace consciousTrace environmentTrace h_body h_conscious h_environment
  exact ⟨trauma_yields_body_consciousness_overflow bodyTrace h_body,
    rumination_yields_thought_consciousness_overflow consciousTrace h_conscious,
    environment_yields_context_overflow environmentTrace h_environment⟩

/-- Compression is the upstream processing account for the frequency-bearing
    emotion index: long traces expose a stable signal carrier at frequency 1. -/
theorem compression_overflow_grounds_emotion_frequency :
    ∀ (observations : List Observation),
    observations.length > 50 →
    ∃ sig, sig ∈ information_sieve observations ∧
      sig.frequency = 1 ∧
      sig.amplitude = 3 ∧ sig.decay_rate = 60 := by
  intro observations h_len
  exact compression_preserves_signal_amplitude observations h_len

/-- The full bridge: compression gives the processing carrier, trauma gives
    body-local overflow, and rumination gives conscious-local overflow. -/
theorem compression_trauma_rumination_share_wave_index :
    ∀ (processingTrace bodyTrace consciousTrace : List Observation),
    processingTrace.length > 50 →
    bodyTrace.length > 0 →
    consciousTrace.length > 50 →
    processingLocalOverflow processingTrace ∧
    bodyLocalOverflow bodyTrace ∧
    consciousLocalOverflow consciousTrace := by
  intro processingTrace bodyTrace consciousTrace h_processing h_body h_conscious
  exact ⟨compression_is_processing_local_overflow processingTrace h_processing,
    trauma_is_body_local_overflow bodyTrace h_body,
    rumination_is_conscious_local_overflow consciousTrace h_conscious⟩

end LocalizedOverflowConsciousness
