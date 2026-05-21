import Gnosis.SyntheticGnosisMeasurement

/-
  SyntheticGnosisThothConsciousness.lean
  ======================================

  A Lean-facing contract for the Thoth runtime observation of a Pneuma
  transcript conscious frame.

  The Rust runtime reads a `pneuma.transcript.consciousness.v1` frame, extracts
  the finite `Gnosis.SyntheticGnosisMeasurement` payload, and folds a bounded
  awareness delta into its conscious swarm node. This file proves the shape of
  that update. It deliberately proves bookkeeping and routing facts only:
  bounded deltas, exact counter projection, and the fold phase attachment.
  It does not prove speaker intent, diagnosis, culture, or semantic authority.
-/

namespace SyntheticGnosisThothConsciousness

open SyntheticGnosisMeasurement

inductive ThothSelfTalkPhase where
  | listen
  | speak
  | reflect
  | fold
  deriving DecidableEq, Repr

structure ThothConsciousNode where
  consciousness : Nat
  value : Nat
  energy : Nat
  phase : ThothSelfTalkPhase
  deriving DecidableEq, Repr

structure PneumaTranscriptConsciousObservation where
  measurement : GnosisRichnessMeasurement
  deriving DecidableEq, Repr

structure ThothPromptFeedbackContext where
  observations : List PneumaTranscriptConsciousObservation
  theoremLabel : String
  renderedLineCount : Nat
  observationalOnly : Bool
  deriving DecidableEq, Repr

inductive NativeConsciousFrameKind where
  | pneumaTranscript
  | thothConversation
  | neurosymbolicToolMarkov
  deriving DecidableEq, Repr

def nativeConsciousFrameKindTag : NativeConsciousFrameKind → String
  | NativeConsciousFrameKind.pneumaTranscript =>
      "pneuma.transcript.consciousness.v1"
  | NativeConsciousFrameKind.thothConversation =>
      "thoth.conversation.consciousness.v1"
  | NativeConsciousFrameKind.neurosymbolicToolMarkov =>
      "thoth.neurosymbolic-tool-markov.v1"

def acceptedNativeConsciousFrameKindTags : List String :=
  [ nativeConsciousFrameKindTag NativeConsciousFrameKind.pneumaTranscript
  ,
    nativeConsciousFrameKindTag NativeConsciousFrameKind.thothConversation
  ,
    nativeConsciousFrameKindTag NativeConsciousFrameKind.neurosymbolicToolMarkov ]

structure NativeConsciousFrameWitness where
  kind : NativeConsciousFrameKind
  payloadByteCount : Nat
  frameByteCount : Nat
  sequence : Nat
  hasNativeBytes : Bool
  observationalOnly : Bool
  deriving DecidableEq, Repr

structure NativePromptFeedbackWitness where
  frames : List NativeConsciousFrameWitness
  acceptedFrameCount : Nat
  renderedLineCount : Nat
  theoremLabel : String
  observationalOnly : Bool
  deriving DecidableEq, Repr

def scoreBand (measurement : GnosisRichnessMeasurement) : Nat :=
  if measurement.scoreLimit = 0 then
    0
  else
    measurement.score * 10 / measurement.scoreLimit

def residueBand (measurement : GnosisRichnessMeasurement) : Nat :=
  measurement.vector.lowConfidenceResidue / 100

def integrityBand (measurement : GnosisRichnessMeasurement) : Nat :=
  measurement.vector.checksumMismatchCount * 5 +
  measurement.vector.auditGapCount * 5

def awarenessDelta (observation : PneumaTranscriptConsciousObservation) : Nat :=
  Nat.min 100
    (scoreBand observation.measurement +
     residueBand observation.measurement +
     integrityBand observation.measurement)

def energyDelta (observation : PneumaTranscriptConsciousObservation) : Nat :=
  Nat.max 1 (observation.measurement.score / 10000)

def observePneumaTranscriptConsciousFrame
    (node : ThothConsciousNode)
    (observation : PneumaTranscriptConsciousObservation) :
    ThothConsciousNode :=
  { consciousness := node.consciousness + awarenessDelta observation
    value := node.value + observation.measurement.score
    energy := node.energy + energyDelta observation
    phase := ThothSelfTalkPhase.fold }

def buildPromptFeedbackContext
    (observations : List PneumaTranscriptConsciousObservation) :
    ThothPromptFeedbackContext :=
  { observations
    theoremLabel :=
      "Gnosis.SyntheticGnosisThothConsciousness.prompt_feedback_non_authority"
    renderedLineCount := observations.length
    observationalOnly := true }

def buildNativeFrameWitness
    (kind : NativeConsciousFrameKind)
    (payloadByteCount frameByteCount sequence : Nat) :
    NativeConsciousFrameWitness :=
  { kind
    payloadByteCount
    frameByteCount
    sequence
    hasNativeBytes := 0 < frameByteCount
    observationalOnly := true }

def buildNativePromptFeedbackWitness
    (frames : List NativeConsciousFrameWitness) :
    NativePromptFeedbackWitness :=
  { frames
    acceptedFrameCount := frames.length
    renderedLineCount := frames.length
    theoremLabel :=
      "Gnosis.SyntheticGnosisThothConsciousness.native_prompt_feedback_non_authority"
    observationalOnly := true }

def ObservationBounded (observation : PneumaTranscriptConsciousObservation) : Prop :=
  awarenessDelta observation ≤ 100

def ObservationFromBoundedMeasurement
    (observation : PneumaTranscriptConsciousObservation) : Prop :=
  ScoreBounded observation.measurement

def ObservationNonAuthority
    (observation : PneumaTranscriptConsciousObservation) : Prop :=
  ObservationalMeasurement observation.measurement

def PromptFeedbackNonAuthority (context : ThothPromptFeedbackContext) : Prop :=
  context.observationalOnly = true

def PromptFeedbackCoversObservations
    (context : ThothPromptFeedbackContext) : Prop :=
  context.renderedLineCount = context.observations.length

def NativeFramePayloadProjects
    (frame : NativeConsciousFrameWitness) : Prop :=
  frame.hasNativeBytes = decide (0 < frame.frameByteCount)

def NativeFramePayloadFits
    (frame : NativeConsciousFrameWitness) : Prop :=
  frame.payloadByteCount ≤ frame.frameByteCount

def NativeFrameNonAuthority
    (frame : NativeConsciousFrameWitness) : Prop :=
  frame.observationalOnly = true

def NativePromptFeedbackNonAuthority
    (witness : NativePromptFeedbackWitness) : Prop :=
  witness.observationalOnly = true

def NativePromptFeedbackCoversFrames
    (witness : NativePromptFeedbackWitness) : Prop :=
  witness.acceptedFrameCount = witness.frames.length ∧
    witness.renderedLineCount = witness.frames.length

def NativeFrameKindKnown
    (_frame : NativeConsciousFrameWitness) : Prop :=
  True

def NativeFrameKindTagProjects
    (frame : NativeConsciousFrameWitness) : Prop :=
  nativeConsciousFrameKindTag frame.kind ∈ acceptedNativeConsciousFrameKindTags

theorem awareness_delta_bounded
    (observation : PneumaTranscriptConsciousObservation) :
    ObservationBounded observation := by
  unfold ObservationBounded awarenessDelta
  exact Nat.min_le_left 100
    (scoreBand observation.measurement +
     residueBand observation.measurement +
     integrityBand observation.measurement)

theorem observation_from_measurement_bounded
    (limit : Nat) (weights : GnosisRichnessWeights)
    (vector : GnosisRichnessVector) :
    ObservationFromBoundedMeasurement
      { measurement := measureSyntheticGnosis limit weights vector } := by
  unfold ObservationFromBoundedMeasurement
  exact measured_score_bounded limit weights vector

theorem observation_non_authority_from_measurement
    (limit : Nat) (weights : GnosisRichnessWeights)
    (vector : GnosisRichnessVector) :
    ObservationNonAuthority
      { measurement := measureSyntheticGnosis limit weights vector } := by
  unfold ObservationNonAuthority
  exact measured_observational_only limit weights vector

theorem observe_projects_consciousness_delta
    (node : ThothConsciousNode)
    (observation : PneumaTranscriptConsciousObservation) :
    (observePneumaTranscriptConsciousFrame node observation).consciousness =
      node.consciousness + awarenessDelta observation := by
  rfl

theorem observe_projects_value_delta
    (node : ThothConsciousNode)
    (observation : PneumaTranscriptConsciousObservation) :
    (observePneumaTranscriptConsciousFrame node observation).value =
      node.value + observation.measurement.score := by
  rfl

theorem observe_projects_energy_delta
    (node : ThothConsciousNode)
    (observation : PneumaTranscriptConsciousObservation) :
    (observePneumaTranscriptConsciousFrame node observation).energy =
      node.energy + energyDelta observation := by
  rfl

theorem observe_routes_to_fold_phase
    (node : ThothConsciousNode)
    (observation : PneumaTranscriptConsciousObservation) :
    (observePneumaTranscriptConsciousFrame node observation).phase =
      ThothSelfTalkPhase.fold := by
  rfl

theorem observe_consciousness_monotone
    (node : ThothConsciousNode)
    (observation : PneumaTranscriptConsciousObservation) :
    node.consciousness ≤
      (observePneumaTranscriptConsciousFrame node observation).consciousness := by
  unfold observePneumaTranscriptConsciousFrame
  exact Nat.le_add_right node.consciousness (awarenessDelta observation)

theorem observe_value_monotone
    (node : ThothConsciousNode)
    (observation : PneumaTranscriptConsciousObservation) :
    node.value ≤ (observePneumaTranscriptConsciousFrame node observation).value := by
  unfold observePneumaTranscriptConsciousFrame
  exact Nat.le_add_right node.value observation.measurement.score

theorem observe_energy_monotone
    (node : ThothConsciousNode)
    (observation : PneumaTranscriptConsciousObservation) :
    node.energy ≤ (observePneumaTranscriptConsciousFrame node observation).energy := by
  unfold observePneumaTranscriptConsciousFrame
  exact Nat.le_add_right node.energy (energyDelta observation)

theorem prompt_feedback_non_authority
    (observations : List PneumaTranscriptConsciousObservation) :
    PromptFeedbackNonAuthority (buildPromptFeedbackContext observations) := by
  rfl

theorem prompt_feedback_covers_observations
    (observations : List PneumaTranscriptConsciousObservation) :
    PromptFeedbackCoversObservations (buildPromptFeedbackContext observations) := by
  rfl

theorem prompt_feedback_empty_has_zero_lines :
    (buildPromptFeedbackContext []).renderedLineCount = 0 := by
  rfl

theorem prompt_feedback_singleton_has_one_line
    (observation : PneumaTranscriptConsciousObservation) :
    (buildPromptFeedbackContext [observation]).renderedLineCount = 1 := by
  rfl

theorem native_frame_payload_projects
    (kind : NativeConsciousFrameKind)
    (payloadByteCount frameByteCount sequence : Nat) :
    NativeFramePayloadProjects
      (buildNativeFrameWitness kind payloadByteCount frameByteCount sequence) := by
  unfold NativeFramePayloadProjects buildNativeFrameWitness
  rfl

theorem native_frame_non_authority
    (kind : NativeConsciousFrameKind)
    (payloadByteCount frameByteCount sequence : Nat) :
    NativeFrameNonAuthority
      (buildNativeFrameWitness kind payloadByteCount frameByteCount sequence) := by
  rfl

theorem native_frame_kind_known
    (frame : NativeConsciousFrameWitness) :
    NativeFrameKindKnown frame := by
  trivial

theorem native_frame_kind_tag_projects
    (frame : NativeConsciousFrameWitness) :
    NativeFrameKindTagProjects frame := by
  unfold NativeFrameKindTagProjects acceptedNativeConsciousFrameKindTags
  cases frame.kind <;> simp [nativeConsciousFrameKindTag]

theorem native_frame_kind_tag_exhaustive
    (kind : NativeConsciousFrameKind) :
    nativeConsciousFrameKindTag kind =
      nativeConsciousFrameKindTag NativeConsciousFrameKind.pneumaTranscript ∨
    nativeConsciousFrameKindTag kind =
      nativeConsciousFrameKindTag NativeConsciousFrameKind.thothConversation ∨
    nativeConsciousFrameKindTag kind =
      nativeConsciousFrameKindTag NativeConsciousFrameKind.neurosymbolicToolMarkov := by
  cases kind <;> simp [nativeConsciousFrameKindTag]

theorem native_frame_payload_fits_when_declared
    (kind : NativeConsciousFrameKind)
    (payloadByteCount frameByteCount sequence : Nat)
    (h : payloadByteCount ≤ frameByteCount) :
    NativeFramePayloadFits
      (buildNativeFrameWitness kind payloadByteCount frameByteCount sequence) := by
  exact h

theorem native_prompt_feedback_non_authority
    (frames : List NativeConsciousFrameWitness) :
    NativePromptFeedbackNonAuthority
      (buildNativePromptFeedbackWitness frames) := by
  rfl

theorem native_prompt_feedback_covers_frames
    (frames : List NativeConsciousFrameWitness) :
    NativePromptFeedbackCoversFrames
      (buildNativePromptFeedbackWitness frames) := by
  constructor <;> rfl

theorem native_prompt_feedback_empty_has_zero_lines :
    (buildNativePromptFeedbackWitness []).renderedLineCount = 0 := by
  rfl

theorem native_prompt_feedback_singleton_has_one_line
    (frame : NativeConsciousFrameWitness) :
    (buildNativePromptFeedbackWitness [frame]).renderedLineCount = 1 := by
  rfl

def witnessThothNode : ThothConsciousNode :=
  { consciousness := 0
    value := 0
    energy := 10
    phase := ThothSelfTalkPhase.listen }

def witnessObservation : PneumaTranscriptConsciousObservation :=
  { measurement := witnessMeasurement }

theorem witness_observation_bounded : ObservationBounded witnessObservation := by
  exact awareness_delta_bounded witnessObservation

theorem witness_observation_routes_to_fold :
    (observePneumaTranscriptConsciousFrame witnessThothNode witnessObservation).phase =
      ThothSelfTalkPhase.fold := by
  decide

theorem witness_observation_updates_consciousness :
    (observePneumaTranscriptConsciousFrame witnessThothNode witnessObservation).consciousness =
      awarenessDelta witnessObservation := by
  rfl

def witnessPromptFeedbackContext : ThothPromptFeedbackContext :=
  buildPromptFeedbackContext [witnessObservation]

theorem witness_prompt_feedback_non_authority :
    PromptFeedbackNonAuthority witnessPromptFeedbackContext := by
  rfl

theorem witness_prompt_feedback_covers_observation :
    PromptFeedbackCoversObservations witnessPromptFeedbackContext := by
  rfl

def witnessNativeConversationFrame : NativeConsciousFrameWitness :=
  buildNativeFrameWitness NativeConsciousFrameKind.thothConversation 1024 1536 99

def witnessNativePromptFeedback : NativePromptFeedbackWitness :=
  buildNativePromptFeedbackWitness [witnessNativeConversationFrame]

theorem witness_native_frame_has_bytes :
    witnessNativeConversationFrame.hasNativeBytes = true := by
  rfl

theorem witness_native_frame_payload_projects :
    NativeFramePayloadProjects witnessNativeConversationFrame := by
  unfold NativeFramePayloadProjects witnessNativeConversationFrame buildNativeFrameWitness
  rfl

theorem witness_native_frame_payload_fits :
    NativeFramePayloadFits witnessNativeConversationFrame := by
  unfold NativeFramePayloadFits witnessNativeConversationFrame buildNativeFrameWitness
  decide

theorem witness_native_frame_kind_tag_projects :
    NativeFrameKindTagProjects witnessNativeConversationFrame := by
  exact native_frame_kind_tag_projects witnessNativeConversationFrame

theorem witness_native_prompt_feedback_non_authority :
    NativePromptFeedbackNonAuthority witnessNativePromptFeedback := by
  rfl

theorem witness_native_prompt_feedback_covers_frame :
    NativePromptFeedbackCoversFrames witnessNativePromptFeedback := by
  unfold NativePromptFeedbackCoversFrames witnessNativePromptFeedback
    buildNativePromptFeedbackWitness witnessNativeConversationFrame buildNativeFrameWitness
  decide

end SyntheticGnosisThothConsciousness
