import Gnosis.EchoChamberAsTaoBowl
import Gnosis.AttentionQKVDecomposition
import Gnosis.SpeakerStandingWaveDiarization

/-
  SemanticToneWaveTabs.lean
  =========================

  Formal contract for sarcasm, irony, and adjacent semantic tone tabs as
  finite standing-wave records in Tao-bowl / attention-head space.

  Runtime calibration supplies the scores:

  * carrier frequency, bowl mode, and Q/K/V head frequency;
  * literal-vs-intended surface strength;
  * phase inversion, expectation violation, and evidence components;
  * confidence as a finite Nat dial.

  Lean proves the honest boundary: projection, threshold, evidence accounting,
  and separation contracts. It does not prove that a person "really meant"
  sarcasm, irony, sincerity, humor, threat, or any other psychological state.

  Imports Tao-bowl, QKV attention, and speaker standing-wave modules so this can
  co-read with `fundamentalMode`, `freqMismatch`, and speaker/head carriers.
  Zero `sorry`, zero new `axiom`.
-/

namespace SemanticToneWaveTabs

open EchoChamberAsTaoBowl
open AttentionQKVDecomposition
open SpeakerStandingWaveDiarization

/-! ## Tone tab records -/

/-- Semantic tone tabs worth tracking separately from raw sentiment.

    `sarcasm` is treated as a sharper irony-like inversion with stronger
    speaker/context evidence. `irony` records expectation/meaning reversal
    without requiring the extra bite of sarcasm. -/
inductive SemanticToneKind where
  | sarcasm
  | irony
  | sincerity
  | humor
  | understatement
  | hyperbole
  | threat
  | invitation
  | uncertainty
  | emphasis
  deriving DecidableEq, Repr

/-- Runtime-extracted tone wave tab.

    All scalar fields are finite calibration dials, not psychological proof.
    The three evidence fields are kept separate so projection theorems can
    preserve provenance: context, speaker history, and listener uptake. -/
structure SemanticToneWaveTab where
  kind : SemanticToneKind
  carrierFrequency : Nat
  bowlFrequency : Nat
  qkvFrequency : Nat
  phaseInversion : Nat
  expectationViolation : Nat
  literalSurface : Nat
  intendedSurface : Nat
  contextEvidence : Nat
  speakerEvidence : Nat
  listenerEvidence : Nat
  confidence : Nat
  deriving DecidableEq, Repr

/-- Compact coordinate projection for tabular storage. -/
def toneCoordinate (tab : SemanticToneWaveTab) :
    SemanticToneKind × Nat × Nat × Nat × Nat × Nat × Nat :=
  (tab.kind, tab.carrierFrequency, tab.bowlFrequency, tab.qkvFrequency,
    tab.phaseInversion, tab.expectationViolation, tab.confidence)

/-- Evidence is additive and finite; runtime decides how each component is
    calibrated before Lean receives the record. -/
def evidenceTotal (tab : SemanticToneWaveTab) : Nat :=
  tab.contextEvidence + tab.speakerEvidence + tab.listenerEvidence

/-- A confidence threshold predicate for downstream filters. -/
def ConfidentAt (threshold : Nat) (tab : SemanticToneWaveTab) : Prop :=
  threshold ≤ tab.confidence

/-- Evidence threshold separated from confidence threshold. -/
def EvidenceAt (threshold : Nat) (tab : SemanticToneWaveTab) : Prop :=
  threshold ≤ evidenceTotal tab

/-- A tab clears both confidence and evidence thresholds. -/
def AcceptedToneAt (confidenceThreshold evidenceThreshold : Nat)
    (tab : SemanticToneWaveTab) : Prop :=
  ConfidentAt confidenceThreshold tab ∧ EvidenceAt evidenceThreshold tab

/-! ## Shape predicates for irony and sarcasm -/

/-- General irony wave: a tone tab marked as irony or sarcasm, with enough
    phase inversion and expectation violation to justify the inversion shape. -/
def IronyWaveAt (inversionThreshold violationThreshold : Nat)
    (tab : SemanticToneWaveTab) : Prop :=
  (tab.kind = SemanticToneKind.irony ∨ tab.kind = SemanticToneKind.sarcasm) ∧
  inversionThreshold ≤ tab.phaseInversion ∧
  violationThreshold ≤ tab.expectationViolation

/-- Sarcasm wave: sarcasm kind, irony-shaped inversion, intended surface at
    least as strong as literal surface, and context/speaker evidence present.

    The last two conjuncts are bookkeeping gates only: they say the runtime
    supplied nonzero provenance, not that the interpretation is certain. -/
def SarcasmWaveAt (inversionThreshold violationThreshold : Nat)
    (tab : SemanticToneWaveTab) : Prop :=
  tab.kind = SemanticToneKind.sarcasm ∧
  inversionThreshold ≤ tab.phaseInversion ∧
  violationThreshold ≤ tab.expectationViolation ∧
  tab.literalSurface ≤ tab.intendedSurface ∧
  0 < tab.contextEvidence ∧
  0 < tab.speakerEvidence

/-- Sincerity is tracked as its own tab: low inversion is supplied as an
    explicit bound from runtime calibration. -/
def SincerityWaveAt (maxInversion : Nat) (tab : SemanticToneWaveTab) : Prop :=
  tab.kind = SemanticToneKind.sincerity ∧ tab.phaseInversion ≤ maxInversion

/-! ## Separation in Tao-bowl / attention-head space -/

/-- Frequency distance for tone tabs. -/
def toneFrequencyDistance (a b : SemanticToneWaveTab) : Nat :=
  Nat.max a.carrierFrequency b.carrierFrequency -
    Nat.min a.carrierFrequency b.carrierFrequency

/-- Two tabs are separated when they carry different semantic labels and their
    carrier frequencies clear a runtime threshold. -/
def ToneSeparatedAt (threshold : Nat) (a b : SemanticToneWaveTab) : Prop :=
  a.kind ≠ b.kind ∧ toneFrequencyDistance a b ≥ threshold

/-- A tab sits on its Tao-bowl carrier exactly when its stored bowl frequency is
    the bowl's fundamental mode. -/
def ToneOnBowlMode (tab : SemanticToneWaveTab) (bowl : TaoBowl) : Prop :=
  tab.bowlFrequency = fundamentalMode bowl

/-- A tab matches an attention head when its QKV carrier is the head frequency. -/
def ToneOnAttentionHead (tab : SemanticToneWaveTab)
    (pattern : AttentionQKVPattern) : Prop :=
  tab.qkvFrequency = pattern.frequency

/-- Speaker coupling keeps the semantic carrier attached to a diarized speaker
    standing wave without proving speaker identity. -/
def ToneOnSpeakerWave (tab : SemanticToneWaveTab) (speaker : SpeakerWave) : Prop :=
  tab.carrierFrequency = speaker.mode

/-! ## Projection theorems -/

theorem tone_coordinate_projects_kind (tab : SemanticToneWaveTab) :
    (toneCoordinate tab).1 = tab.kind := by
  rfl

theorem tone_coordinate_projects_carrier (tab : SemanticToneWaveTab) :
    (toneCoordinate tab).2.1 = tab.carrierFrequency := by
  rfl

theorem tone_coordinate_projects_bowl (tab : SemanticToneWaveTab) :
    (toneCoordinate tab).2.2.1 = tab.bowlFrequency := by
  rfl

theorem tone_coordinate_projects_qkv (tab : SemanticToneWaveTab) :
    (toneCoordinate tab).2.2.2.1 = tab.qkvFrequency := by
  rfl

theorem tone_coordinate_projects_confidence (tab : SemanticToneWaveTab) :
    (toneCoordinate tab).2.2.2.2.2.2 = tab.confidence := by
  rfl

theorem accepted_tone_projects_confidence
    (confidenceThreshold evidenceThreshold : Nat) (tab : SemanticToneWaveTab)
    (h : AcceptedToneAt confidenceThreshold evidenceThreshold tab) :
    ConfidentAt confidenceThreshold tab :=
  h.1

theorem accepted_tone_projects_evidence
    (confidenceThreshold evidenceThreshold : Nat) (tab : SemanticToneWaveTab)
    (h : AcceptedToneAt confidenceThreshold evidenceThreshold tab) :
    EvidenceAt evidenceThreshold tab :=
  h.2

theorem sarcasm_wave_is_irony_wave
    (inversionThreshold violationThreshold : Nat) (tab : SemanticToneWaveTab)
    (h : SarcasmWaveAt inversionThreshold violationThreshold tab) :
    IronyWaveAt inversionThreshold violationThreshold tab := by
  unfold SarcasmWaveAt at h
  unfold IronyWaveAt
  exact ⟨Or.inr h.1, h.2.1, h.2.2.1⟩

theorem sarcasm_wave_projects_kind
    (inversionThreshold violationThreshold : Nat) (tab : SemanticToneWaveTab)
    (h : SarcasmWaveAt inversionThreshold violationThreshold tab) :
    tab.kind = SemanticToneKind.sarcasm :=
  h.1

theorem irony_wave_projects_inversion
    (inversionThreshold violationThreshold : Nat) (tab : SemanticToneWaveTab)
    (h : IronyWaveAt inversionThreshold violationThreshold tab) :
    inversionThreshold ≤ tab.phaseInversion :=
  h.2.1

theorem irony_wave_projects_expectation_violation
    (inversionThreshold violationThreshold : Nat) (tab : SemanticToneWaveTab)
    (h : IronyWaveAt inversionThreshold violationThreshold tab) :
    violationThreshold ≤ tab.expectationViolation :=
  h.2.2

theorem sarcasm_wave_projects_context_evidence
    (inversionThreshold violationThreshold : Nat) (tab : SemanticToneWaveTab)
    (h : SarcasmWaveAt inversionThreshold violationThreshold tab) :
    0 < tab.contextEvidence :=
  h.2.2.2.2.1

theorem sarcasm_wave_projects_speaker_evidence
    (inversionThreshold violationThreshold : Nat) (tab : SemanticToneWaveTab)
    (h : SarcasmWaveAt inversionThreshold violationThreshold tab) :
    0 < tab.speakerEvidence :=
  h.2.2.2.2.2

theorem tone_separation_symmetric (threshold : Nat)
    (a b : SemanticToneWaveTab)
    (h : ToneSeparatedAt threshold a b) :
    ToneSeparatedAt threshold b a := by
  unfold ToneSeparatedAt toneFrequencyDistance at h ⊢
  exact ⟨fun hba => h.1 hba.symm, by
    simpa [Nat.max_comm, Nat.min_comm] using h.2⟩

theorem tone_on_bowl_mode_zero_mismatch
    (tab : SemanticToneWaveTab) (bowl : TaoBowl)
    (h : ToneOnBowlMode tab bowl) :
    freqMismatch bowl tab.bowlFrequency = 0 := by
  unfold ToneOnBowlMode at h
  unfold freqMismatch
  rw [h]
  simp

theorem tone_on_attention_head_projects_frequency
    (tab : SemanticToneWaveTab) (pattern : AttentionQKVPattern)
    (h : ToneOnAttentionHead tab pattern) :
    tab.qkvFrequency = pattern.frequency :=
  h

theorem tone_on_speaker_wave_projects_mode
    (tab : SemanticToneWaveTab) (speaker : SpeakerWave)
    (h : ToneOnSpeakerWave tab speaker) :
    tab.carrierFrequency = speaker.mode :=
  h

/-! ## Concrete finite tabs -/

def sarcasmTab : SemanticToneWaveTab where
  kind := SemanticToneKind.sarcasm
  carrierFrequency := 13
  bowlFrequency := 5
  qkvFrequency := 8
  phaseInversion := 9
  expectationViolation := 8
  literalSurface := 3
  intendedSurface := 9
  contextEvidence := 4
  speakerEvidence := 5
  listenerEvidence := 2
  confidence := 91

def ironyTab : SemanticToneWaveTab where
  kind := SemanticToneKind.irony
  carrierFrequency := 11
  bowlFrequency := 5
  qkvFrequency := 7
  phaseInversion := 7
  expectationViolation := 9
  literalSurface := 5
  intendedSurface := 7
  contextEvidence := 5
  speakerEvidence := 1
  listenerEvidence := 3
  confidence := 84

def sincerityTab : SemanticToneWaveTab where
  kind := SemanticToneKind.sincerity
  carrierFrequency := 2
  bowlFrequency := 2
  qkvFrequency := 2
  phaseInversion := 0
  expectationViolation := 1
  literalSurface := 8
  intendedSurface := 8
  contextEvidence := 3
  speakerEvidence := 3
  listenerEvidence := 3
  confidence := 88

def uncertaintyTab : SemanticToneWaveTab where
  kind := SemanticToneKind.uncertainty
  carrierFrequency := 17
  bowlFrequency := 6
  qkvFrequency := 12
  phaseInversion := 2
  expectationViolation := 4
  literalSurface := 4
  intendedSurface := 5
  contextEvidence := 2
  speakerEvidence := 1
  listenerEvidence := 4
  confidence := 73

theorem sarcasmTab_is_sarcasm_wave :
    SarcasmWaveAt 7 7 sarcasmTab := by
  unfold SarcasmWaveAt sarcasmTab
  decide

theorem sarcasmTab_is_irony_wave :
    IronyWaveAt 7 7 sarcasmTab :=
  sarcasm_wave_is_irony_wave 7 7 sarcasmTab sarcasmTab_is_sarcasm_wave

theorem ironyTab_is_irony_wave :
    IronyWaveAt 7 7 ironyTab := by
  unfold IronyWaveAt ironyTab
  decide

theorem sarcasmTab_confident_at_ninety :
    ConfidentAt 90 sarcasmTab := by
  unfold ConfidentAt sarcasmTab
  decide

theorem sincerityTab_low_inversion :
    SincerityWaveAt 1 sincerityTab := by
  unfold SincerityWaveAt sincerityTab
  decide

theorem sarcasm_irony_tabs_separated :
    ToneSeparatedAt 2 sarcasmTab ironyTab := by
  unfold ToneSeparatedAt toneFrequencyDistance sarcasmTab ironyTab
  decide

theorem sarcasm_evidence_total_value :
    evidenceTotal sarcasmTab = 11 := by
  unfold evidenceTotal sarcasmTab
  decide

end SemanticToneWaveTabs
