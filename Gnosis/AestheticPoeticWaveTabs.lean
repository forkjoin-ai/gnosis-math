import Gnosis.SpeakerStandingWaveDiarization
import Gnosis.BeautyOptimality
import Gnosis.PoetryLattice
import Gnosis.PoetricFormsNoiseMapping
import Gnosis.HarmonyAsConstructiveInterference

/-
  AestheticPoeticWaveTabs.lean
  ============================

  Finite transcript tabs for beauty, poetic resonance, harmony, and poetic
  form/noise-color projections. Lean proves projection and boundedness only;
  it does not prove that a passage is truly beautiful.
-/

namespace AestheticPoeticWaveTabs

open SpeakerStandingWaveDiarization

inductive AestheticWaveKind where
  | beauty
  | poeticResonance
  | harmony
  | sublime
  | elegance
  | lyricDensity
  | metaphorPressure
  | formality
  | noiseColor
  deriving DecidableEq, Repr

inductive RuntimePoeticForm where
  | triton
  | hexon
  | haiku
  | tanka
  | sestina
  | freeVerse
  deriving DecidableEq, Repr

inductive RuntimeNoiseColor where
  | brown
  | brownPink
  | pink
  | pinkWhite
  | whiteViolet
  | violetUltraviolet
  | ultraviolet
  deriving DecidableEq, Repr

structure AestheticPoeticTab where
  kind : AestheticWaveKind
  carrier : ParagraphCarrier
  confidence : Nat
  evidence : Nat
  ropelengthEstimate : Nat
  rhythmFactor : Nat
  repetitionScore : Nat
  fractalScore : Nat
  poeticForm : Option RuntimePoeticForm
  noiseColor : Option RuntimeNoiseColor
  deriving DecidableEq, Repr

def AestheticBoundedBy (limit : Nat) (tab : AestheticPoeticTab) : Prop :=
  tab.confidence ≤ limit ∧ tab.evidence ≤ limit ∧
  tab.rhythmFactor ≤ limit ∧ tab.repetitionScore ≤ limit ∧
  tab.fractalScore ≤ limit

def AestheticAttachedToCarrier (tab : AestheticPoeticTab) (carrier : ParagraphCarrier) : Prop :=
  tab.carrier = carrier

def SafeAestheticProjection (limit : Nat) (tag : ParagraphTranscriptTag)
    (tab : AestheticPoeticTab) : Prop :=
  TagAttachedToCarrier tag ∧ AestheticAttachedToCarrier tab tag.carrier ∧
  TagConfidenceBoundedBy limit tag ∧ AestheticBoundedBy limit tab

def HasPoetryLatticeProjection (tab : AestheticPoeticTab) : Prop :=
  tab.poeticForm.isSome ∧ 0 < tab.ropelengthEstimate

def HasNoiseColorProjection (tab : AestheticPoeticTab) : Prop :=
  tab.noiseColor.isSome

theorem safe_aesthetic_projection_projects_attachment
    (limit : Nat) (tag : ParagraphTranscriptTag) (tab : AestheticPoeticTab)
    (h : SafeAestheticProjection limit tag tab) :
    AestheticAttachedToCarrier tab tag.carrier :=
  h.2.1

theorem poetry_projection_has_positive_ropelength
    (tab : AestheticPoeticTab) (h : HasPoetryLatticeProjection tab) :
    0 < tab.ropelengthEstimate :=
  h.2

def witnessCarrier : ParagraphCarrier :=
  { paragraphIndex := 0, carrierFrequency := 610, amplitude := 17,
    phase := 17, speakerHint := none }

def witnessTag : ParagraphTranscriptTag :=
  { paragraphIndex := 0, carrier := witnessCarrier, speakerLabel := 3,
    speakerConfidence := 76, role := SpeakerRoleKind.explainer, roleConfidence := 72,
    emotion := EmotionAxisKind.awe, emotionConfidence := 70,
    mood := MoodKind.reflective, moodConfidence := 64,
    prosodyShape := ProsodyShapeKind.flowing, prosodyConfidence := 62,
    dominantTone := some TranscriptToneKind.wonder, toneConfidence := 66 }

def witnessPoeticTab : AestheticPoeticTab :=
  { kind := AestheticWaveKind.poeticResonance, carrier := witnessCarrier,
    confidence := 80, evidence := 44, ropelengthEstimate := 17,
    rhythmFactor := 3, repetitionScore := 12, fractalScore := 0,
    poeticForm := some RuntimePoeticForm.haiku,
    noiseColor := some RuntimeNoiseColor.brown }

example : AestheticBoundedBy 100 witnessPoeticTab := by
  simp [AestheticBoundedBy, witnessPoeticTab]

example : SafeAestheticProjection 100 witnessTag witnessPoeticTab := by
  simp [SafeAestheticProjection, TagAttachedToCarrier,
    AestheticAttachedToCarrier, TagConfidenceBoundedBy, AestheticBoundedBy,
    witnessTag, witnessPoeticTab, witnessCarrier]

example : HasPoetryLatticeProjection witnessPoeticTab := by
  simp [HasPoetryLatticeProjection, witnessPoeticTab]

end AestheticPoeticWaveTabs
