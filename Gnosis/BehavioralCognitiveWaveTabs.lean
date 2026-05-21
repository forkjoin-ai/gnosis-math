import Gnosis.SpeakerStandingWaveDiarization

/-
  BehavioralCognitiveWaveTabs.lean
  =================================

  Finite contracts for behavioral and cognitive transcript wave tabs.

  Runtime scoring supplies bounded observations such as anxiety, vulnerability,
  charisma, charm, certainty, and repair. Lean proves projection and boundedness
  for the received records. It does not prove intent, pathology, personality
  identity, or diagnosis.
-/

namespace BehavioralCognitiveWaveTabs

open SpeakerStandingWaveDiarization

/-! ## Runtime tab kinds -/

inductive BehavioralWaveKind where
  | charisma
  | charm
  | anxiety
  | vulnerability
  | defensiveness
  | dominance
  | trust
  | rapport
  | avoidance
  | openness
  | cognitiveLoad
  | certainty
  | selfDisclosure
  | repair
  | invitation
  deriving DecidableEq, Repr

inductive PersonalityLayerKind where
  | layer1_temperament
  | layer2_attachment
  | layer3_traits
  | layer4_behaviors
  | layer5_mental_health
  | layer6_history
  | layer7_environment
  deriving DecidableEq, Repr

structure BehavioralWaveTab where
  kind : BehavioralWaveKind
  carrier : ParagraphCarrier
  personalityLayer : PersonalityLayerKind
  confidence : Nat
  evidence : Nat
  arousal : Nat
  disclosure : Nat
  agency : Nat
  deriving DecidableEq, Repr

def behavioralCoordinate (tab : BehavioralWaveTab) :
    BehavioralWaveKind × Nat × PersonalityLayerKind × Nat :=
  (tab.kind, tab.carrier.paragraphIndex, tab.personalityLayer, tab.confidence)

def ConfidentAt (threshold : Nat) (tab : BehavioralWaveTab) : Prop :=
  threshold ≤ tab.confidence

def EvidenceAt (threshold : Nat) (tab : BehavioralWaveTab) : Prop :=
  threshold ≤ tab.evidence

def TabAttachedToCarrier (tab : BehavioralWaveTab) (carrier : ParagraphCarrier) : Prop :=
  tab.carrier = carrier

def ConfidenceBoundedBy (limit : Nat) (tab : BehavioralWaveTab) : Prop :=
  tab.confidence ≤ limit ∧ tab.evidence ≤ limit ∧
  tab.arousal ≤ limit ∧ tab.disclosure ≤ limit ∧ tab.agency ≤ limit

def SafeBehavioralProjection (limit : Nat) (tag : ParagraphTranscriptTag)
    (tab : BehavioralWaveTab) : Prop :=
  TagAttachedToCarrier tag ∧ TabAttachedToCarrier tab tag.carrier ∧
  TagConfidenceBoundedBy limit tag ∧ ConfidenceBoundedBy limit tab

def CharismaWaveAt (threshold : Nat) (tab : BehavioralWaveTab) : Prop :=
  tab.kind = BehavioralWaveKind.charisma ∧ threshold ≤ tab.confidence ∧ threshold ≤ tab.agency

def CharmWaveAt (threshold : Nat) (tab : BehavioralWaveTab) : Prop :=
  tab.kind = BehavioralWaveKind.charm ∧ threshold ≤ tab.confidence

def AnxietyWaveAt (threshold : Nat) (tab : BehavioralWaveTab) : Prop :=
  tab.kind = BehavioralWaveKind.anxiety ∧ threshold ≤ tab.confidence ∧ threshold ≤ tab.arousal

def VulnerabilityWaveAt (threshold : Nat) (tab : BehavioralWaveTab) : Prop :=
  tab.kind = BehavioralWaveKind.vulnerability ∧ threshold ≤ tab.confidence ∧ threshold ≤ tab.disclosure

/-! ## Projection theorems -/

theorem behavioral_coordinate_projects_kind (tab : BehavioralWaveTab) :
    (behavioralCoordinate tab).1 = tab.kind := by
  rfl

theorem behavioral_coordinate_projects_carrier_index (tab : BehavioralWaveTab) :
    (behavioralCoordinate tab).2.1 = tab.carrier.paragraphIndex := by
  rfl

theorem behavioral_coordinate_projects_layer (tab : BehavioralWaveTab) :
    (behavioralCoordinate tab).2.2.1 = tab.personalityLayer := by
  rfl

theorem behavioral_coordinate_projects_confidence (tab : BehavioralWaveTab) :
    (behavioralCoordinate tab).2.2.2 = tab.confidence := by
  rfl

theorem safe_behavioral_projection_projects_tag_attachment
    (limit : Nat) (tag : ParagraphTranscriptTag) (tab : BehavioralWaveTab)
    (h : SafeBehavioralProjection limit tag tab) :
    TagAttachedToCarrier tag :=
  h.1

theorem safe_behavioral_projection_projects_tab_attachment
    (limit : Nat) (tag : ParagraphTranscriptTag) (tab : BehavioralWaveTab)
    (h : SafeBehavioralProjection limit tag tab) :
    TabAttachedToCarrier tab tag.carrier :=
  h.2.1

theorem charisma_wave_projects_confidence
    (threshold : Nat) (tab : BehavioralWaveTab)
    (h : CharismaWaveAt threshold tab) :
    ConfidentAt threshold tab :=
  h.2.1

theorem anxiety_wave_projects_evidence_shape
    (threshold : Nat) (tab : BehavioralWaveTab)
    (h : AnxietyWaveAt threshold tab) :
    threshold ≤ tab.arousal :=
  h.2.2

theorem vulnerability_wave_projects_disclosure
    (threshold : Nat) (tab : BehavioralWaveTab)
    (h : VulnerabilityWaveAt threshold tab) :
    threshold ≤ tab.disclosure :=
  h.2.2

/-! ## Concrete decidable witness -/

def witnessCarrier : ParagraphCarrier :=
  { paragraphIndex := 0, carrierFrequency := 440, amplitude := 12,
    phase := 90, speakerHint := none }

def witnessTranscriptTag : ParagraphTranscriptTag :=
  { paragraphIndex := 0, carrier := witnessCarrier, speakerLabel := 1,
    speakerConfidence := 71, role := SpeakerRoleKind.witness, roleConfidence := 66,
    emotion := EmotionAxisKind.care, emotionConfidence := 64,
    mood := MoodKind.reflective, moodConfidence := 58,
    prosodyShape := ProsodyShapeKind.flowing, prosodyConfidence := 60,
    dominantTone := some TranscriptToneKind.sincerity, toneConfidence := 54 }

def witnessVulnerabilityTab : BehavioralWaveTab :=
  { kind := BehavioralWaveKind.vulnerability, carrier := witnessCarrier,
    personalityLayer := PersonalityLayerKind.layer2_attachment,
    confidence := 74, evidence := 48, arousal := 22, disclosure := 80, agency := 34 }

example : ConfidenceBoundedBy 100 witnessVulnerabilityTab := by
  simp [ConfidenceBoundedBy, witnessVulnerabilityTab]

example : SafeBehavioralProjection 100 witnessTranscriptTag witnessVulnerabilityTab := by
  simp [SafeBehavioralProjection, TagAttachedToCarrier, TabAttachedToCarrier,
    TagConfidenceBoundedBy, ConfidenceBoundedBy, witnessTranscriptTag,
    witnessVulnerabilityTab, witnessCarrier]

example : VulnerabilityWaveAt 70 witnessVulnerabilityTab := by
  simp [VulnerabilityWaveAt, witnessVulnerabilityTab]

end BehavioralCognitiveWaveTabs
