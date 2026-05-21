import Gnosis.SpeakerStandingWaveDiarization

/-
  CognitiveBiasWaveTabs.lean
  ==========================

  Finite observational tabs for cognitive-bias cues in transcript text. These
  are System-2 engagement hints, not proofs that a person is biased.
-/

namespace CognitiveBiasWaveTabs

open SpeakerStandingWaveDiarization

inductive CognitiveBiasKind where
  | wysiati
  | substitution
  | anchoring
  | availability
  | affect_heuristic
  | confirmation_bias
  | sunk_cost
  | planning_fallacy
  deriving DecidableEq, Repr

structure CognitiveLoadFactors where
  emotionalIntensity : Nat
  topicComplexity : Nat
  relationshipStakes : Nat
  temporalPressure : Nat
  uncertaintyLevel : Nat
  valuesInvolvement : Nat
  deriving DecidableEq, Repr

structure CognitiveBiasTab where
  kind : CognitiveBiasKind
  carrier : ParagraphCarrier
  confidence : Nat
  evidence : Nat
  system1Confidence : Nat
  needsSystem2Endorsement : Bool
  load : CognitiveLoadFactors
  deriving DecidableEq, Repr

def LoadBoundedBy (limit : Nat) (load : CognitiveLoadFactors) : Prop :=
  load.emotionalIntensity ≤ limit ∧ load.topicComplexity ≤ limit ∧
  load.relationshipStakes ≤ limit ∧ load.temporalPressure ≤ limit ∧
  load.uncertaintyLevel ≤ limit ∧ load.valuesInvolvement ≤ limit

def BiasBoundedBy (limit : Nat) (tab : CognitiveBiasTab) : Prop :=
  tab.confidence ≤ limit ∧ tab.evidence ≤ limit ∧
  tab.system1Confidence ≤ limit ∧ LoadBoundedBy limit tab.load

def BiasAttachedToCarrier (tab : CognitiveBiasTab) (carrier : ParagraphCarrier) : Prop :=
  tab.carrier = carrier

def SafeBiasProjection (limit : Nat) (tag : ParagraphTranscriptTag)
    (tab : CognitiveBiasTab) : Prop :=
  TagAttachedToCarrier tag ∧ BiasAttachedToCarrier tab tag.carrier ∧
  TagConfidenceBoundedBy limit tag ∧ BiasBoundedBy limit tab

def BiasConfidentAt (threshold : Nat) (tab : CognitiveBiasTab) : Prop :=
  threshold ≤ tab.confidence

theorem safe_bias_projection_projects_attachment
    (limit : Nat) (tag : ParagraphTranscriptTag) (tab : CognitiveBiasTab)
    (h : SafeBiasProjection limit tag tab) :
    BiasAttachedToCarrier tab tag.carrier :=
  h.2.1

theorem confident_bias_projects_confidence
    (threshold : Nat) (tab : CognitiveBiasTab)
    (h : BiasConfidentAt threshold tab) :
    threshold ≤ tab.confidence :=
  h

def witnessCarrier : ParagraphCarrier :=
  { paragraphIndex := 0, carrierFrequency := 510, amplitude := 8,
    phase := 45, speakerHint := none }

def witnessTag : ParagraphTranscriptTag :=
  { paragraphIndex := 0, carrier := witnessCarrier, speakerLabel := 2,
    speakerConfidence := 72, role := SpeakerRoleKind.challenger, roleConfidence := 68,
    emotion := EmotionAxisKind.confidence, emotionConfidence := 70,
    mood := MoodKind.corrective, moodConfidence := 66,
    prosodyShape := ProsodyShapeKind.emphatic, prosodyConfidence := 64,
    dominantTone := some TranscriptToneKind.emphasis, toneConfidence := 62 }

def witnessLoad : CognitiveLoadFactors :=
  { emotionalIntensity := 30, topicComplexity := 40, relationshipStakes := 10,
    temporalPressure := 0, uncertaintyLevel := 15, valuesInvolvement := 20 }

def witnessWysiati : CognitiveBiasTab :=
  { kind := CognitiveBiasKind.wysiati, carrier := witnessCarrier,
    confidence := 74, evidence := 30, system1Confidence := 60,
    needsSystem2Endorsement := true, load := witnessLoad }

example : BiasBoundedBy 100 witnessWysiati := by
  simp [BiasBoundedBy, LoadBoundedBy, witnessWysiati, witnessLoad]

example : SafeBiasProjection 100 witnessTag witnessWysiati := by
  simp [SafeBiasProjection, TagAttachedToCarrier, BiasAttachedToCarrier,
    TagConfidenceBoundedBy, BiasBoundedBy, LoadBoundedBy, witnessTag,
    witnessWysiati, witnessCarrier, witnessLoad]

end CognitiveBiasWaveTabs
