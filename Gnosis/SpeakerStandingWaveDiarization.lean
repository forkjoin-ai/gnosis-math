import Init
import Gnosis.EchoChamberAsTaoBowl
import Gnosis.AttentionQKVDecomposition

/-
  SpeakerStandingWaveDiarization.lean
  ===================================

  Formal contract for speaker identification as a Tao-bowl / attention-head
  standing-wave partition problem.

  Runtime diarization supplies calibrated finite scores:

  * each paragraph has an acoustic-semantic carrier;
  * each candidate speaker group has a standing wave summarizing its paragraphs;
  * a conversation partition is good when groups resonate internally, remain
    separated from one another, and keep the whole transcript accounted for.

  This file intentionally does not claim that a cosine threshold proves a human
  identity. It proves the bookkeeping boundary: "same speaker" is represented
  as a provisional standing-wave group, while person identity remains outside
  the acoustic cluster unless anchored by additional evidence.

  Imports Tao-bowl and QKV attention modules so downstream code can co-read this
  with `fundamentalMode`, `qFactor`, and Q/K/V gating. Zero `sorry`, zero new
  `axiom`.
-/

namespace SpeakerStandingWaveDiarization

open EchoChamberAsTaoBowl
open AttentionQKVDecomposition

/-! ## Paragraph carriers -/

/-- A paragraph-level carrier extracted from transcript text plus audio.

    All scalar fields are finite calibration dials:
    * `carrierFrequency` is the dominant standing dimension / mode index.
    * `amplitude` is strength / confidence.
    * `phase` is a coarse phase bucket.
    * `paragraphIndex` preserves transcript order.
    * `speakerHint` is optional external evidence, not an identity proof. -/
structure ParagraphCarrier where
  paragraphIndex : Nat
  carrierFrequency : Nat
  amplitude : Nat
  phase : Nat
  speakerHint : Option Nat
  deriving DecidableEq, Repr

/-! ## Turn segmentation boundary -/

/-- A turn-like span produced by runtime segmentation before diarization.

    The runtime may split one transcript paragraph into multiple turns when
    conversational cues indicate a speaker handoff. Lean does not prove the
    linguistic split is correct; it records the bookkeeping certificate the
    runtime must preserve:

    * `sourceParagraph` remembers the original paragraph.
    * `turnIndex` orders turns within that paragraph.
    * `beginOffset` and `endOffset` are finite span bounds.
    * `carrier` is the diarization carrier extracted for this turn. -/
structure TurnSpan where
  sourceParagraph : Nat
  turnIndex : Nat
  beginOffset : Nat
  endOffset : Nat
  carrier : ParagraphCarrier
  deriving DecidableEq, Repr

/-- A turn span is well-bounded when its finite offsets are ordered and the
    extracted carrier still points at the source paragraph. -/
def WellBoundedTurnSpan (turn : TurnSpan) : Prop :=
  turn.beginOffset ≤ turn.endOffset ∧
  turn.carrier.paragraphIndex = turn.sourceParagraph

/-- A segmentation is locally well-bounded when every emitted turn span carries
    ordered offsets and remembers its source paragraph. -/
def WellBoundedSegmentation (turns : List TurnSpan) : Prop :=
  ∀ turn ∈ turns, WellBoundedTurnSpan turn

/-- Turn segmentation covers exactly the carrier list the diarizer will see.
    This is the formal counterpart to the runtime `splitTranscriptTurnText`
    handoff: after splitting, downstream speaker/emotion tags operate on the
    projected turn carriers. -/
def SegmentationCoversCarriers (turns : List TurnSpan)
    (carriers : List ParagraphCarrier) : Prop :=
  turns.map (fun turn => turn.carrier) = carriers

/-- The residuals left by a segmentation against a carrier list.  The runtime
    should present an empty list here before asking speaker waves to explain the
    conversation. -/
def segmentationResiduals (turns : List TurnSpan)
    (carriers : List ParagraphCarrier) : List ParagraphCarrier :=
  if turns.map (fun turn => turn.carrier) = carriers then [] else carriers

/-- A segmentation has no carrier residuals exactly when its projected turn
    carriers match the carrier list consumed by diarization. -/
def NoSegmentationResiduals (turns : List TurnSpan)
    (carriers : List ParagraphCarrier) : Prop :=
  segmentationResiduals turns carriers = []

/-! ## Transcript tag annotations -/

/-- Runtime speaker-role tags. These are provisional conversation roles, not
    person identity claims. -/
inductive SpeakerRoleKind where
  | host
  | explainer
  | challenger
  | witness
  deriving DecidableEq, Repr

/-- Runtime affect axis tags used by the transcript transcript pipeline. -/
inductive EmotionAxisKind where
  | awe
  | curiosity
  | confidence
  | tension
  | frustration
  | care
  | neutral
  deriving DecidableEq, Repr

/-- Runtime mood tags. -/
inductive MoodKind where
  | settled
  | inquisitive
  | charged
  | reflective
  | corrective
  deriving DecidableEq, Repr

/-- Runtime prosody-shape tags. Text-only transcript estimates these from punctuation
    and conversational cues; acoustic runtime can replace them with measured
    prosody. -/
inductive ProsodyShapeKind where
  | clipped
  | flowing
  | emphatic
  | hesitant
  | rising
  deriving DecidableEq, Repr

/-- Runtime semantic-tone tags mirrored locally to avoid a module cycle with
    `SemanticToneWaveTabs`, which imports this diarization contract. -/
inductive TranscriptToneKind where
  | sarcasm
  | irony
  | sincerity
  | uncertainty
  | emphasis
  | correction
  | wonder
  deriving DecidableEq, Repr

/-- A paragraph/turn transcript tag as a finite annotation over an extracted
    carrier. Every confidence field is a runtime calibration dial. -/
structure ParagraphTranscriptTag where
  paragraphIndex : Nat
  carrier : ParagraphCarrier
  speakerLabel : Nat
  speakerConfidence : Nat
  role : SpeakerRoleKind
  roleConfidence : Nat
  emotion : EmotionAxisKind
  emotionConfidence : Nat
  mood : MoodKind
  moodConfidence : Nat
  prosodyShape : ProsodyShapeKind
  prosodyConfidence : Nat
  dominantTone : Option TranscriptToneKind
  toneConfidence : Nat
  deriving DecidableEq, Repr

/-- A tag is attached to its carrier when the tag's index agrees with the
    carrier index. -/
def TagAttachedToCarrier (tag : ParagraphTranscriptTag) : Prop :=
  tag.paragraphIndex = tag.carrier.paragraphIndex

/-- A tag is attached to a turn span when it annotates exactly that turn's
    projected carrier. -/
def TagAttachedToTurn (tag : ParagraphTranscriptTag) (turn : TurnSpan) : Prop :=
  tag.carrier = turn.carrier ∧ TagAttachedToCarrier tag

/-- A tag list covers a turn segmentation when projecting tag carriers gives the
    same carrier list as projecting turn carriers. -/
def TagsCoverTurns (tags : List ParagraphTranscriptTag)
    (turns : List TurnSpan) : Prop :=
  tags.map (fun tag => tag.carrier) = turns.map (fun turn => turn.carrier)

/-- Runtime confidence bounds for all finite tag dials. -/
def TagConfidenceBoundedBy (limit : Nat) (tag : ParagraphTranscriptTag) : Prop :=
  tag.speakerConfidence ≤ limit ∧
  tag.roleConfidence ≤ limit ∧
  tag.emotionConfidence ≤ limit ∧
  tag.moodConfidence ≤ limit ∧
  tag.prosodyConfidence ≤ limit ∧
  tag.toneConfidence ≤ limit

/-- A whole tag list is locally well-formed when every tag attaches to its
    carrier and every confidence dial is bounded by the runtime limit. -/
def WellFormedTranscriptTags (limit : Nat)
    (tags : List ParagraphTranscriptTag) : Prop :=
  ∀ tag ∈ tags, TagAttachedToCarrier tag ∧ TagConfidenceBoundedBy limit tag

/-- A candidate speaker standing wave: a subset of paragraphs with one shared
    carrier mode and a Tao bowl recording rim/void/damping context. -/
structure SpeakerWave where
  label : Nat
  paragraphs : List ParagraphCarrier
  mode : Nat
  coherence : Nat
  bowl : TaoBowl
  deriving Repr

/-- A candidate diarization partition for the transcript. -/
structure ConversationPartition where
  waves : List SpeakerWave
  residualParagraphs : List ParagraphCarrier
  deriving Repr

/-! ## Local resonance and cross-speaker separation -/

/-- Frequency distance between a paragraph carrier and a speaker wave. -/
def carrierMismatch (p : ParagraphCarrier) (w : SpeakerWave) : Nat :=
  if p.carrierFrequency ≤ w.mode then w.mode - p.carrierFrequency else p.carrierFrequency - w.mode

/-- Paragraph `p` is on-mode for speaker wave `w`. -/
def ParagraphOnWave (p : ParagraphCarrier) (w : SpeakerWave) : Prop :=
  carrierMismatch p w = 0

/-- A speaker wave has internal resonance when every paragraph it contains is
    on the shared mode, has non-zero amplitude, and the wave has non-zero
    coherence. -/
def InternalResonance (w : SpeakerWave) : Prop :=
  0 < w.coherence ∧
  ∀ p ∈ w.paragraphs, ParagraphOnWave p w ∧ 0 < p.amplitude

/-- Phase separation is symmetric by using absolute phase distance. -/
def phaseDistance (a b : Nat) : Nat :=
  Nat.max a b - Nat.min a b

/-- Two speaker waves are separated when their modes differ and their phase
    distance clears a runtime-calibrated threshold. This is the Lean version of
    "directionally orthogonal-ish"; exact cosine geometry lives in runtime
    measurement. -/
def CrossSpeakerSeparatedAt (threshold : Nat) (a b : SpeakerWave) : Prop :=
  a.mode ≠ b.mode ∧ phaseDistance a.mode b.mode ≥ threshold

/-- Every pair of distinct labels in a partition is separated. -/
def PairwiseSeparatedAt (threshold : Nat) (partition : ConversationPartition) : Prop :=
  ∀ a ∈ partition.waves, ∀ b ∈ partition.waves,
    a.label ≠ b.label → CrossSpeakerSeparatedAt threshold a b

/-! ## Whole-conversation equilibrium -/

/-- No unaccounted paragraphs: the diarization explains the transcript instead
    of leaving residual chunks outside the speaker bowls. -/
def NoResidualParagraphs (partition : ConversationPartition) : Prop :=
  partition.residualParagraphs = []

/-- The whole transcript stays in equilibrium when every speaker wave resonates,
    speaker waves remain separated, and no paragraph is left outside the
    partition. -/
def ConversationEquilibriumAt (threshold : Nat) (partition : ConversationPartition) : Prop :=
  (∀ w ∈ partition.waves, InternalResonance w) ∧
  PairwiseSeparatedAt threshold partition ∧
  NoResidualParagraphs partition

/-! ## Scoring contract for "truest standing wave" selection -/

/-- Candidate score components supplied by runtime measurement.

    Larger is better for the first four fields; penalties are subtracted through
    `partitionScore`. The arithmetic is deliberately saturating via `Nat` minus:
    too much fragmentation or over-merge can collapse a candidate to zero. -/
structure PartitionScore where
  withinSpeakerResonance : Nat
  crossSpeakerSeparation : Nat
  temporalTurnConsistency : Nat
  transcriptEquilibrium : Nat
  fragmentationPenalty : Nat
  overmergePenalty : Nat
  deriving DecidableEq, Repr

/-- Positive evidence before penalties. -/
def positiveEvidence (s : PartitionScore) : Nat :=
  s.withinSpeakerResonance +
  s.crossSpeakerSeparation +
  s.temporalTurnConsistency +
  s.transcriptEquilibrium

/-- Total penalty against over-fragmenting one speaker or over-merging multiple
    speakers into one bowl. -/
def totalPenalty (s : PartitionScore) : Nat :=
  s.fragmentationPenalty + s.overmergePenalty

/-- Saturating objective: the score never goes negative. -/
def partitionScore (s : PartitionScore) : Nat :=
  positiveEvidence s - totalPenalty s

/-- A measured candidate couples a partition with its runtime score. -/
structure MeasuredPartition where
  partition : ConversationPartition
  score : PartitionScore
  deriving Repr

/-- The "truest" candidate is one no other candidate beats under the objective.
    This avoids claiming a computable argmax exists for every runtime search
    space; the runtime can present a finite winner plus this no-better witness. -/
def IsTruestStandingWavePartition (candidate : MeasuredPartition)
    (candidates : List MeasuredPartition) : Prop :=
  candidate ∈ candidates ∧
  ∀ other ∈ candidates, partitionScore other.score ≤ partitionScore candidate.score

/-! ## Projection theorems -/

theorem well_bounded_turn_span_projects_source (turn : TurnSpan)
    (h : WellBoundedTurnSpan turn) :
    turn.carrier.paragraphIndex = turn.sourceParagraph :=
  h.2

theorem well_bounded_turn_span_offsets_ordered (turn : TurnSpan)
    (h : WellBoundedTurnSpan turn) :
    turn.beginOffset ≤ turn.endOffset :=
  h.1

theorem segmentation_coverage_no_residuals (turns : List TurnSpan)
    (carriers : List ParagraphCarrier)
    (h : SegmentationCoversCarriers turns carriers) :
    NoSegmentationResiduals turns carriers := by
  unfold NoSegmentationResiduals segmentationResiduals
  exact if_pos h

theorem no_segmentation_residuals_from_projected_carriers (turns : List TurnSpan) :
    NoSegmentationResiduals turns (turns.map (fun turn => turn.carrier)) := by
  apply segmentation_coverage_no_residuals
  unfold SegmentationCoversCarriers
  rfl

theorem segmentation_projected_carrier_mem (turns : List TurnSpan)
    (carriers : List ParagraphCarrier)
    (h : SegmentationCoversCarriers turns carriers) :
    ∀ carrier ∈ carriers, ∃ turn ∈ turns, turn.carrier = carrier := by
  intro carrier hCarrier
  unfold SegmentationCoversCarriers at h
  rw [← h] at hCarrier
  exact List.mem_map.mp hCarrier

theorem well_bounded_segmentation_carriers_remember_source
    (turns : List TurnSpan)
    (h : WellBoundedSegmentation turns) :
    ∀ turn ∈ turns, turn.carrier.paragraphIndex = turn.sourceParagraph := by
  intro turn hTurn
  exact (h turn hTurn).2

theorem partition_no_residuals_from_segmentation
    (turns : List TurnSpan)
    (carriers : List ParagraphCarrier)
    (partition : ConversationPartition)
    (hSeg : SegmentationCoversCarriers turns carriers)
    (hPart : partition.residualParagraphs = segmentationResiduals turns carriers) :
    NoResidualParagraphs partition := by
  unfold NoResidualParagraphs
  rw [hPart]
  unfold segmentationResiduals
  exact if_pos hSeg

theorem tag_attached_to_turn_projects_carrier (tag : ParagraphTranscriptTag)
    (turn : TurnSpan)
    (h : TagAttachedToTurn tag turn) :
    tag.carrier = turn.carrier :=
  h.1

theorem tag_attached_to_turn_projects_index (tag : ParagraphTranscriptTag)
    (turn : TurnSpan)
    (h : TagAttachedToTurn tag turn) :
    tag.paragraphIndex = turn.carrier.paragraphIndex := by
  rw [h.2, h.1]

theorem well_formed_tag_projects_attachment (limit : Nat)
    (tags : List ParagraphTranscriptTag)
    (h : WellFormedTranscriptTags limit tags) :
    ∀ tag ∈ tags, TagAttachedToCarrier tag := by
  intro tag hTag
  exact (h tag hTag).1

theorem well_formed_tag_projects_confidence_bound (limit : Nat)
    (tags : List ParagraphTranscriptTag)
    (h : WellFormedTranscriptTags limit tags) :
    ∀ tag ∈ tags, TagConfidenceBoundedBy limit tag := by
  intro tag hTag
  exact (h tag hTag).2

theorem tags_cover_turns_project_carriers (tags : List ParagraphTranscriptTag)
    (turns : List TurnSpan)
    (h : TagsCoverTurns tags turns) :
    tags.map (fun tag => tag.carrier) = turns.map (fun turn => turn.carrier) :=
  h

theorem tags_cover_segmentation_carriers (tags : List ParagraphTranscriptTag)
    (turns : List TurnSpan)
    (carriers : List ParagraphCarrier)
    (hTags : TagsCoverTurns tags turns)
    (hSeg : SegmentationCoversCarriers turns carriers) :
    tags.map (fun tag => tag.carrier) = carriers := by
  unfold TagsCoverTurns at hTags
  unfold SegmentationCoversCarriers at hSeg
  rw [hTags, hSeg]

theorem tags_cover_no_segmentation_residuals (tags : List ParagraphTranscriptTag)
    (turns : List TurnSpan)
    (carriers : List ParagraphCarrier)
    (_hTags : TagsCoverTurns tags turns)
    (hSeg : SegmentationCoversCarriers turns carriers) :
    NoSegmentationResiduals turns carriers := by
  exact segmentation_coverage_no_residuals turns carriers hSeg

theorem tag_carrier_mem_of_tags_cover_turns (tags : List ParagraphTranscriptTag)
    (turns : List TurnSpan)
    (h : TagsCoverTurns tags turns) :
    ∀ tag ∈ tags, ∃ turn ∈ turns, turn.carrier = tag.carrier := by
  intro tag hTag
  unfold TagsCoverTurns at h
  have hCarrier : tag.carrier ∈ turns.map (fun turn => turn.carrier) := by
    rw [← h]
    exact List.mem_map_of_mem (f := fun tag : ParagraphTranscriptTag => tag.carrier) hTag
  rcases List.mem_map.mp hCarrier with ⟨turn, hTurn, hEq⟩
  exact ⟨turn, hTurn, hEq⟩

theorem covered_tag_preserves_source_when_turns_well_bounded
    (tags : List ParagraphTranscriptTag)
    (turns : List TurnSpan)
    (hTags : TagsCoverTurns tags turns)
    (hTurns : WellBoundedSegmentation turns) :
    ∀ tag ∈ tags, ∃ turn ∈ turns,
      turn.carrier = tag.carrier ∧
      turn.carrier.paragraphIndex = turn.sourceParagraph := by
  intro tag hTag
  rcases tag_carrier_mem_of_tags_cover_turns tags turns hTags tag hTag with ⟨turn, hTurn, hEq⟩
  exact ⟨turn, hTurn, hEq, (hTurns turn hTurn).2⟩

theorem internal_resonance_has_positive_coherence (w : SpeakerWave)
    (h : InternalResonance w) : 0 < w.coherence :=
  h.1

theorem internal_resonance_paragraph_on_wave (w : SpeakerWave)
    (h : InternalResonance w) :
    ∀ p ∈ w.paragraphs, ParagraphOnWave p w := by
  intro p hp
  exact (h.2 p hp).1

theorem internal_resonance_paragraph_amplitude_positive (w : SpeakerWave)
    (h : InternalResonance w) :
    ∀ p ∈ w.paragraphs, 0 < p.amplitude := by
  intro p hp
  exact (h.2 p hp).2

theorem phaseDistance_comm (a b : Nat) :
    phaseDistance a b = phaseDistance b a := by
  unfold phaseDistance
  simp [Nat.max_comm, Nat.min_comm]

theorem cross_speaker_separation_symmetric (threshold : Nat) (a b : SpeakerWave)
    (h : CrossSpeakerSeparatedAt threshold a b) :
    CrossSpeakerSeparatedAt threshold b a := by
  unfold CrossSpeakerSeparatedAt at h ⊢
  exact ⟨fun hba => h.1 hba.symm, by simpa [phaseDistance_comm b.mode a.mode] using h.2⟩

theorem equilibrium_all_waves_resonate (threshold : Nat) (partition : ConversationPartition)
    (h : ConversationEquilibriumAt threshold partition) :
    ∀ w ∈ partition.waves, InternalResonance w :=
  h.1

theorem equilibrium_pairwise_separated (threshold : Nat) (partition : ConversationPartition)
    (h : ConversationEquilibriumAt threshold partition) :
    PairwiseSeparatedAt threshold partition :=
  h.2.1

theorem equilibrium_has_no_residuals (threshold : Nat) (partition : ConversationPartition)
    (h : ConversationEquilibriumAt threshold partition) :
    NoResidualParagraphs partition :=
  h.2.2

theorem truest_partition_is_candidate (candidate : MeasuredPartition)
    (candidates : List MeasuredPartition)
    (h : IsTruestStandingWavePartition candidate candidates) :
    candidate ∈ candidates :=
  h.1

theorem truest_partition_no_candidate_scores_higher (candidate other : MeasuredPartition)
    (candidates : List MeasuredPartition)
    (h : IsTruestStandingWavePartition candidate candidates)
    (hOther : other ∈ candidates) :
    partitionScore other.score ≤ partitionScore candidate.score :=
  h.2 other hOther

/-- A perfect unpenalized score is exactly its positive evidence. -/
theorem partition_score_unpenalized (s : PartitionScore)
    (hFrag : s.fragmentationPenalty = 0) (hMerge : s.overmergePenalty = 0) :
    partitionScore s = positiveEvidence s := by
  unfold partitionScore totalPenalty
  simp [hFrag, hMerge]

/-! ## Bridges to the existing Tao-bowl and attention-head vocabulary -/

/-- A speaker wave whose mode equals its bowl's fundamental mode is exactly
    on the Tao-bowl carrier. -/
def SpeakerWaveOnBowlMode (w : SpeakerWave) : Prop :=
  w.mode = fundamentalMode w.bowl

theorem speaker_wave_on_bowl_mode_zero_mismatch (w : SpeakerWave)
    (h : SpeakerWaveOnBowlMode w) :
    freqMismatch w.bowl w.mode = 0 := by
  unfold SpeakerWaveOnBowlMode at h
  unfold freqMismatch
  rw [h]
  simp

/-- Runtime attention extraction can be carried as the Q/K/V witness for a
    speaker wave. This bridge records the exact predicate already used by the
    attention formalization. -/
def SpeakerWaveHasQKVGatedCarrier (_w : SpeakerWave) (pattern : AttentionQKVPattern) : Prop :=
  value_standing_and_gated pattern = true

theorem speaker_qkv_carrier_projects_gate (w : SpeakerWave)
    (pattern : AttentionQKVPattern)
    (h : SpeakerWaveHasQKVGatedCarrier w pattern) :
    is_query_standing pattern = true ∧
      is_key_standing pattern = true ∧
      is_value_standing pattern = true ∧
      is_value_gated pattern = true :=
  intersection_implies_high_selectivity pattern h

end SpeakerStandingWaveDiarization
