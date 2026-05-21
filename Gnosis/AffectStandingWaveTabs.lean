import Gnosis.VibesAsWaveInference
import Gnosis.AffectMatrixAgencyAxis
import Gnosis.SpeakerStandingWaveDiarization

/-
  AffectStandingWaveTabs.lean
  ===========================

  Runtime transcript affect tabs projected into the Lean-canonical affect
  catalog from `VibesAsWaveInference`. Lean proves finite coordinate
  projection, carrier attachment, and confidence bounds. It does not prove that
  a speaker truly feels the emotion.
-/

namespace AffectStandingWaveTabs

open SpeakerStandingWaveDiarization
open VibesAsWaveInference
open LocalizedOverflowConsciousness

structure AffectStandingWaveTab where
  kind : AffectKind
  carrier : ParagraphCarrier
  locale : OverflowLocale
  valence : OverflowValence
  frequency : Nat
  intensity : Nat
  arousal : Nat
  dominance : Nat
  tendency : AffectTendency
  confidence : Nat
  evidence : Nat
  deriving Repr

def affectCoordinate (tab : AffectStandingWaveTab) :
    AffectKind × OverflowLocale × OverflowValence × Nat × Nat × Nat × Nat × AffectTendency :=
  (tab.kind, tab.locale, tab.valence, tab.frequency, tab.intensity,
    tab.arousal, tab.dominance, tab.tendency)

def TabMatchesLeanCatalog (tab : AffectStandingWaveTab) : Prop :=
  let canonical := affectOfKind tab.kind
  tab.locale = canonical.emotion.locale ∧
  tab.valence = canonical.emotion.valence ∧
  tab.frequency = canonical.emotion.frequency ∧
  tab.intensity = canonical.emotion.intensity ∧
  tab.arousal = canonical.arousal ∧
  tab.dominance = canonical.dominance ∧
  tab.tendency = canonical.tendency

def ConfidenceBoundedBy (limit : Nat) (tab : AffectStandingWaveTab) : Prop :=
  tab.confidence ≤ limit ∧ tab.evidence ≤ limit

def TabAttachedToCarrier (tab : AffectStandingWaveTab) (carrier : ParagraphCarrier) : Prop :=
  tab.carrier = carrier

def SafeAffectProjection (limit : Nat) (tag : ParagraphTranscriptTag)
    (tab : AffectStandingWaveTab) : Prop :=
  TagAttachedToCarrier tag ∧ TabAttachedToCarrier tab tag.carrier ∧
  TagConfidenceBoundedBy limit tag ∧ ConfidenceBoundedBy limit tab ∧
  TabMatchesLeanCatalog tab

theorem affect_coordinate_projects_kind (tab : AffectStandingWaveTab) :
    (affectCoordinate tab).1 = tab.kind := by
  rfl

theorem affect_coordinate_projects_locale (tab : AffectStandingWaveTab) :
    (affectCoordinate tab).2.1 = tab.locale := by
  rfl

theorem affect_coordinate_projects_valence (tab : AffectStandingWaveTab) :
    (affectCoordinate tab).2.2.1 = tab.valence := by
  rfl

theorem catalog_match_projects_frequency (tab : AffectStandingWaveTab)
    (h : TabMatchesLeanCatalog tab) :
    tab.frequency = (affectOfKind tab.kind).emotion.frequency :=
  h.2.2.1

theorem safe_affect_projection_projects_attachment
    (limit : Nat) (tag : ParagraphTranscriptTag) (tab : AffectStandingWaveTab)
    (h : SafeAffectProjection limit tag tab) :
    TabAttachedToCarrier tab tag.carrier :=
  h.2.1

def witnessCarrier : ParagraphCarrier :=
  { paragraphIndex := 0, carrierFrequency := 440, amplitude := 10,
    phase := 90, speakerHint := none }

def witnessTag : ParagraphTranscriptTag :=
  { paragraphIndex := 0, carrier := witnessCarrier, speakerLabel := 1,
    speakerConfidence := 80, role := SpeakerRoleKind.witness, roleConfidence := 70,
    emotion := EmotionAxisKind.awe, emotionConfidence := 75,
    mood := MoodKind.reflective, moodConfidence := 65,
    prosodyShape := ProsodyShapeKind.flowing, prosodyConfidence := 60,
    dominantTone := some TranscriptToneKind.wonder, toneConfidence := 70 }

def witnessAweTab : AffectStandingWaveTab :=
  { kind := AffectKind.awe, carrier := witnessCarrier,
    locale := (affectOfKind AffectKind.awe).emotion.locale,
    valence := (affectOfKind AffectKind.awe).emotion.valence,
    frequency := (affectOfKind AffectKind.awe).emotion.frequency,
    intensity := (affectOfKind AffectKind.awe).emotion.intensity,
    arousal := (affectOfKind AffectKind.awe).arousal,
    dominance := (affectOfKind AffectKind.awe).dominance,
    tendency := (affectOfKind AffectKind.awe).tendency,
    confidence := 82, evidence := 48 }

example : TabMatchesLeanCatalog witnessAweTab := by
  simp [TabMatchesLeanCatalog, witnessAweTab]

example : SafeAffectProjection 100 witnessTag witnessAweTab := by
  simp [SafeAffectProjection, TagAttachedToCarrier, TabAttachedToCarrier,
    TagConfidenceBoundedBy, ConfidenceBoundedBy, TabMatchesLeanCatalog,
    witnessTag, witnessAweTab, witnessCarrier]

end AffectStandingWaveTabs
