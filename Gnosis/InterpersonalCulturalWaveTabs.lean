import Gnosis.BehavioralCognitiveWaveTabs

/-
  InterpersonalCulturalWaveTabs.lean
  ===================================

  Finite contracts for interpersonal dynamics and cultural undertones attached
  to Pneuma transcript tags.

  These tabs are calibrated observations. Lean proves bounded confidence,
  carrier attachment, evidence projection, and safe projection into transcript
  certificates. It does not prove true intent, culture, status, pathology, or
  personality.
-/

namespace InterpersonalCulturalWaveTabs

open SpeakerStandingWaveDiarization
open BehavioralCognitiveWaveTabs

inductive InterpersonalDynamicKind where
  | rapport
  | dominance
  | submission
  | repair
  | rupture
  | mirroring
  | boundarySetting
  | defensiveness
  | careSeeking
  | statusPlay
  | trustBuilding
  deriving DecidableEq, Repr

inductive CulturalUndertoneKind where
  | individualist
  | collectivist
  | honor
  | bureaucratic
  | academic
  | spiritual
  | technical
  | therapeutic
  | classStatus
  | institutionalTrust
  | antiInstitutional
  deriving DecidableEq, Repr

structure InterpersonalDynamicTab where
  kind : InterpersonalDynamicKind
  carrier : ParagraphCarrier
  confidence : Nat
  evidence : Nat
  socialValence : Nat
  repairPotential : Nat
  deriving DecidableEq, Repr

structure CulturalUndertoneTab where
  kind : CulturalUndertoneKind
  carrier : ParagraphCarrier
  confidence : Nat
  evidence : Nat
  contextGrounding : Nat
  deriving DecidableEq, Repr

def dynamicCoordinate (tab : InterpersonalDynamicTab) :
    InterpersonalDynamicKind × Nat × Nat :=
  (tab.kind, tab.carrier.paragraphIndex, tab.confidence)

def culturalCoordinate (tab : CulturalUndertoneTab) :
    CulturalUndertoneKind × Nat × Nat :=
  (tab.kind, tab.carrier.paragraphIndex, tab.confidence)

def DynamicConfidenceBoundedBy (limit : Nat) (tab : InterpersonalDynamicTab) : Prop :=
  tab.confidence ≤ limit ∧ tab.evidence ≤ limit ∧
  tab.socialValence ≤ limit ∧ tab.repairPotential ≤ limit

def CulturalConfidenceBoundedBy (limit : Nat) (tab : CulturalUndertoneTab) : Prop :=
  tab.confidence ≤ limit ∧ tab.evidence ≤ limit ∧ tab.contextGrounding ≤ limit

def DynamicAttachedToCarrier (tab : InterpersonalDynamicTab) (carrier : ParagraphCarrier) : Prop :=
  tab.carrier = carrier

def CulturalAttachedToCarrier (tab : CulturalUndertoneTab) (carrier : ParagraphCarrier) : Prop :=
  tab.carrier = carrier

def DynamicEvidenceAt (threshold : Nat) (tab : InterpersonalDynamicTab) : Prop :=
  threshold ≤ tab.evidence

def CulturalEvidenceAt (threshold : Nat) (tab : CulturalUndertoneTab) : Prop :=
  threshold ≤ tab.evidence

def SafeInterpersonalProjection (limit : Nat) (tag : ParagraphTranscriptTag)
    (tab : InterpersonalDynamicTab) : Prop :=
  TagAttachedToCarrier tag ∧ DynamicAttachedToCarrier tab tag.carrier ∧
  TagConfidenceBoundedBy limit tag ∧ DynamicConfidenceBoundedBy limit tab

def SafeCulturalProjection (limit : Nat) (tag : ParagraphTranscriptTag)
    (tab : CulturalUndertoneTab) : Prop :=
  TagAttachedToCarrier tag ∧ CulturalAttachedToCarrier tab tag.carrier ∧
  TagConfidenceBoundedBy limit tag ∧ CulturalConfidenceBoundedBy limit tab

def RapportWaveAt (threshold : Nat) (tab : InterpersonalDynamicTab) : Prop :=
  tab.kind = InterpersonalDynamicKind.rapport ∧ threshold ≤ tab.confidence

def DominanceWaveAt (threshold : Nat) (tab : InterpersonalDynamicTab) : Prop :=
  tab.kind = InterpersonalDynamicKind.dominance ∧ threshold ≤ tab.confidence

def RepairWaveAt (threshold : Nat) (tab : InterpersonalDynamicTab) : Prop :=
  tab.kind = InterpersonalDynamicKind.repair ∧
  threshold ≤ tab.confidence ∧ threshold ≤ tab.repairPotential

def TechnicalUndertoneAt (threshold : Nat) (tab : CulturalUndertoneTab) : Prop :=
  tab.kind = CulturalUndertoneKind.technical ∧ threshold ≤ tab.confidence

def SpiritualUndertoneAt (threshold : Nat) (tab : CulturalUndertoneTab) : Prop :=
  tab.kind = CulturalUndertoneKind.spiritual ∧ threshold ≤ tab.confidence

def InstitutionalFrictionAt (threshold : Nat) (tab : CulturalUndertoneTab) : Prop :=
  tab.kind = CulturalUndertoneKind.antiInstitutional ∧
  threshold ≤ tab.confidence ∧ threshold ≤ tab.contextGrounding

/-! ## Projection theorems -/

theorem dynamic_coordinate_projects_kind (tab : InterpersonalDynamicTab) :
    (dynamicCoordinate tab).1 = tab.kind := by
  rfl

theorem dynamic_coordinate_projects_confidence (tab : InterpersonalDynamicTab) :
    (dynamicCoordinate tab).2.2 = tab.confidence := by
  rfl

theorem cultural_coordinate_projects_kind (tab : CulturalUndertoneTab) :
    (culturalCoordinate tab).1 = tab.kind := by
  rfl

theorem cultural_coordinate_projects_confidence (tab : CulturalUndertoneTab) :
    (culturalCoordinate tab).2.2 = tab.confidence := by
  rfl

theorem safe_interpersonal_projection_projects_attachment
    (limit : Nat) (tag : ParagraphTranscriptTag) (tab : InterpersonalDynamicTab)
    (h : SafeInterpersonalProjection limit tag tab) :
    DynamicAttachedToCarrier tab tag.carrier :=
  h.2.1

theorem safe_cultural_projection_projects_attachment
    (limit : Nat) (tag : ParagraphTranscriptTag) (tab : CulturalUndertoneTab)
    (h : SafeCulturalProjection limit tag tab) :
    CulturalAttachedToCarrier tab tag.carrier :=
  h.2.1

theorem repair_wave_projects_repair_potential
    (threshold : Nat) (tab : InterpersonalDynamicTab)
    (h : RepairWaveAt threshold tab) :
    threshold ≤ tab.repairPotential :=
  h.2.2

theorem institutional_friction_projects_grounding
    (threshold : Nat) (tab : CulturalUndertoneTab)
    (h : InstitutionalFrictionAt threshold tab) :
    threshold ≤ tab.contextGrounding :=
  h.2.2

/-! ## Concrete decidable witness -/

def witnessRepairDynamic : InterpersonalDynamicTab :=
  { kind := InterpersonalDynamicKind.repair,
    carrier := BehavioralCognitiveWaveTabs.witnessCarrier,
    confidence := 72, evidence := 50, socialValence := 64, repairPotential := 80 }

def witnessTechnicalUndertone : CulturalUndertoneTab :=
  { kind := CulturalUndertoneKind.technical,
    carrier := BehavioralCognitiveWaveTabs.witnessCarrier,
    confidence := 76, evidence := 52, contextGrounding := 74 }

example : DynamicConfidenceBoundedBy 100 witnessRepairDynamic := by
  simp [DynamicConfidenceBoundedBy, witnessRepairDynamic]

example :
    SafeInterpersonalProjection 100
      BehavioralCognitiveWaveTabs.witnessTranscriptTag witnessRepairDynamic := by
  simp [SafeInterpersonalProjection, TagAttachedToCarrier, DynamicAttachedToCarrier,
    TagConfidenceBoundedBy, DynamicConfidenceBoundedBy,
    BehavioralCognitiveWaveTabs.witnessTranscriptTag,
    BehavioralCognitiveWaveTabs.witnessCarrier, witnessRepairDynamic]

example : RepairWaveAt 70 witnessRepairDynamic := by
  simp [RepairWaveAt, witnessRepairDynamic]

example : CulturalConfidenceBoundedBy 100 witnessTechnicalUndertone := by
  simp [CulturalConfidenceBoundedBy, witnessTechnicalUndertone]

example :
    SafeCulturalProjection 100
      BehavioralCognitiveWaveTabs.witnessTranscriptTag witnessTechnicalUndertone := by
  simp [SafeCulturalProjection, TagAttachedToCarrier, CulturalAttachedToCarrier,
    TagConfidenceBoundedBy, CulturalConfidenceBoundedBy,
    BehavioralCognitiveWaveTabs.witnessTranscriptTag,
    BehavioralCognitiveWaveTabs.witnessCarrier, witnessTechnicalUndertone]

example : TechnicalUndertoneAt 70 witnessTechnicalUndertone := by
  simp [TechnicalUndertoneAt, witnessTechnicalUndertone]

end InterpersonalCulturalWaveTabs
