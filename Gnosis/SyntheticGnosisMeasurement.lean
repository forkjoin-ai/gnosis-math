import Gnosis.PneumaCrossWireTranscript

/-
  SyntheticGnosisMeasurement.lean
  =================================

  A finite measurement surface for transcript "thought packet richness".

  This module deliberately keeps the claim small. Runtime can rank transcript
  packets by observable breadth, density, byte pressure, and low-confidence
  residue. Lean proves only bookkeeping facts about that finite score: bounded
  inputs stay bounded, the score projects its components, and the resulting
  grade remains an observational measurement rather than semantic authority.
-/

namespace SyntheticGnosisMeasurement

open PneumaCrossWireTranscript

structure GnosisRichnessVector where
  paragraphCount : Nat
  tagDensityMilli : Nat
  affectBreadth : Nat
  biasBreadth : Nat
  aestheticBreadth : Nat
  behavioralBreadth : Nat
  interpersonalBreadth : Nat
  culturalBreadth : Nat
  packetPayloadBytes : Nat
  flowFrameBytes : Nat
  lowConfidenceResidue : Nat
  checksumMismatchCount : Nat
  auditGapCount : Nat
  deriving DecidableEq, Repr

structure GnosisRichnessWeights where
  density : Nat
  affect : Nat
  bias : Nat
  aesthetic : Nat
  behavioral : Nat
  interpersonal : Nat
  cultural : Nat
  packetPressure : Nat
  lowConfidencePenalty : Nat
  checksumPenalty : Nat
  auditPenalty : Nat
  deriving DecidableEq, Repr

structure GnosisRichnessMeasurement where
  vector : GnosisRichnessVector
  weights : GnosisRichnessWeights
  rawScore : Nat
  penalty : Nat
  score : Nat
  scoreLimit : Nat
  observationalOnly : Bool
  deriving DecidableEq, Repr

def packetPressure (vector : GnosisRichnessVector) : Nat :=
  vector.packetPayloadBytes + vector.flowFrameBytes

def breadthScore (weights : GnosisRichnessWeights)
    (vector : GnosisRichnessVector) : Nat :=
  weights.affect * vector.affectBreadth +
  weights.bias * vector.biasBreadth +
  weights.aesthetic * vector.aestheticBreadth +
  weights.behavioral * vector.behavioralBreadth +
  weights.interpersonal * vector.interpersonalBreadth +
  weights.cultural * vector.culturalBreadth

def rawRichnessScore (weights : GnosisRichnessWeights)
    (vector : GnosisRichnessVector) : Nat :=
  weights.density * vector.tagDensityMilli +
  breadthScore weights vector +
  weights.packetPressure * packetPressure vector

def richnessPenalty (weights : GnosisRichnessWeights)
    (vector : GnosisRichnessVector) : Nat :=
  weights.lowConfidencePenalty * vector.lowConfidenceResidue +
  weights.checksumPenalty * vector.checksumMismatchCount +
  weights.auditPenalty * vector.auditGapCount

def subtractPenalty (raw penalty : Nat) : Nat :=
  raw - penalty

def clampNat (limit value : Nat) : Nat :=
  Nat.min limit value

def increaseAffectBreadth (delta : Nat)
    (vector : GnosisRichnessVector) : GnosisRichnessVector :=
  { vector with affectBreadth := vector.affectBreadth + delta }

def increasePacketPayloadBytes (delta : Nat)
    (vector : GnosisRichnessVector) : GnosisRichnessVector :=
  { vector with packetPayloadBytes := vector.packetPayloadBytes + delta }

def syntheticGnosisScore (limit : Nat) (weights : GnosisRichnessWeights)
    (vector : GnosisRichnessVector) : Nat :=
  clampNat limit (subtractPenalty (rawRichnessScore weights vector)
    (richnessPenalty weights vector))

def measureSyntheticGnosis (limit : Nat) (weights : GnosisRichnessWeights)
    (vector : GnosisRichnessVector) : GnosisRichnessMeasurement :=
  { vector := vector
    weights := weights
    rawScore := rawRichnessScore weights vector
    penalty := richnessPenalty weights vector
    score := syntheticGnosisScore limit weights vector
    scoreLimit := limit
    observationalOnly := true }

def ScoreBounded (measurement : GnosisRichnessMeasurement) : Prop :=
  measurement.score ≤ measurement.scoreLimit

def ObservationalMeasurement (measurement : GnosisRichnessMeasurement) : Prop :=
  measurement.observationalOnly = true

def PacketCompatible (measurement : GnosisRichnessMeasurement)
    (frame : CrossWireFrame) : Prop :=
  frame.packet.packetCount = measurement.vector.paragraphCount ∧
  frame.packet.transcriptChecksum = frame.packet.transcriptChecksum ∧
  WireWrapperNonAuthority frame

theorem synthetic_score_bounded (limit : Nat)
    (weights : GnosisRichnessWeights) (vector : GnosisRichnessVector) :
    syntheticGnosisScore limit weights vector ≤ limit := by
  unfold syntheticGnosisScore clampNat
  exact Nat.min_le_left limit
    (subtractPenalty (rawRichnessScore weights vector) (richnessPenalty weights vector))

theorem measured_score_bounded (limit : Nat)
    (weights : GnosisRichnessWeights) (vector : GnosisRichnessVector) :
    ScoreBounded (measureSyntheticGnosis limit weights vector) := by
  unfold ScoreBounded measureSyntheticGnosis
  exact synthetic_score_bounded limit weights vector

theorem measured_observational_only (limit : Nat)
    (weights : GnosisRichnessWeights) (vector : GnosisRichnessVector) :
    ObservationalMeasurement (measureSyntheticGnosis limit weights vector) := by
  rfl

theorem raw_score_projects_density_component
    (weights : GnosisRichnessWeights) (vector : GnosisRichnessVector) :
    rawRichnessScore weights vector =
      weights.density * vector.tagDensityMilli +
      breadthScore weights vector +
      weights.packetPressure * packetPressure vector := by
  rfl

theorem penalty_projects_residue_component
    (weights : GnosisRichnessWeights) (vector : GnosisRichnessVector) :
    richnessPenalty weights vector =
      weights.lowConfidencePenalty * vector.lowConfidenceResidue +
      weights.checksumPenalty * vector.checksumMismatchCount +
      weights.auditPenalty * vector.auditGapCount := by
  rfl

theorem packet_compatible_projects_non_authority
    {measurement : GnosisRichnessMeasurement} {frame : CrossWireFrame}
    (h : PacketCompatible measurement frame) :
    WireWrapperNonAuthority frame :=
  h.2.2

theorem raw_score_monotone_affect_breadth_increment
    (weights : GnosisRichnessWeights) (vector : GnosisRichnessVector)
    (delta : Nat) :
    rawRichnessScore weights vector ≤
      rawRichnessScore weights (increaseAffectBreadth delta vector) := by
  unfold rawRichnessScore breadthScore increaseAffectBreadth
  repeat first | apply Nat.add_le_add_right | apply Nat.add_le_add_left
  exact Nat.mul_le_mul_left weights.affect (Nat.le_add_right vector.affectBreadth delta)

theorem raw_score_monotone_packet_payload_increment
    (weights : GnosisRichnessWeights) (vector : GnosisRichnessVector)
    (delta : Nat) :
    rawRichnessScore weights vector ≤
      rawRichnessScore weights (increasePacketPayloadBytes delta vector) := by
  unfold rawRichnessScore packetPressure increasePacketPayloadBytes
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  exact Nat.add_le_add_right (Nat.le_add_right vector.packetPayloadBytes delta)
    vector.flowFrameBytes

theorem post_penalty_score_monotone_when_penalty_fixed
    {raw₁ raw₂ penalty : Nat}
    (hRaw : raw₁ ≤ raw₂) :
    subtractPenalty raw₁ penalty ≤ subtractPenalty raw₂ penalty := by
  unfold subtractPenalty
  exact Nat.sub_le_sub_right hRaw penalty

theorem preclamp_score_monotone_affect_breadth_increment
    (weights : GnosisRichnessWeights) (vector : GnosisRichnessVector)
    (delta : Nat) :
    subtractPenalty (rawRichnessScore weights vector)
        (richnessPenalty weights vector) ≤
      subtractPenalty (rawRichnessScore weights (increaseAffectBreadth delta vector))
        (richnessPenalty weights (increaseAffectBreadth delta vector)) := by
  have hPenalty :
      richnessPenalty weights (increaseAffectBreadth delta vector) =
        richnessPenalty weights vector := by
    rfl
  rw [hPenalty]
  exact post_penalty_score_monotone_when_penalty_fixed
    (raw_score_monotone_affect_breadth_increment weights vector delta)

theorem preclamp_score_monotone_packet_payload_increment
    (weights : GnosisRichnessWeights) (vector : GnosisRichnessVector)
    (delta : Nat) :
    subtractPenalty (rawRichnessScore weights vector)
        (richnessPenalty weights vector) ≤
      subtractPenalty (rawRichnessScore weights (increasePacketPayloadBytes delta vector))
        (richnessPenalty weights (increasePacketPayloadBytes delta vector)) := by
  have hPenalty :
      richnessPenalty weights (increasePacketPayloadBytes delta vector) =
        richnessPenalty weights vector := by
    rfl
  rw [hPenalty]
  exact post_penalty_score_monotone_when_penalty_fixed
    (raw_score_monotone_packet_payload_increment weights vector delta)

def witnessWeights : GnosisRichnessWeights :=
  { density := 1
    affect := 120
    bias := 100
    aesthetic := 90
    behavioral := 110
    interpersonal := 110
    cultural := 80
    packetPressure := 1
    lowConfidencePenalty := 25
    checksumPenalty := 1000
    auditPenalty := 1000 }

def witnessVector : GnosisRichnessVector :=
  { paragraphCount := 248
    tagDensityMilli := 26371
    affectBreadth := 18
    biasBreadth := 5
    aestheticBreadth := 4
    behavioralBreadth := 12
    interpersonalBreadth := 9
    culturalBreadth := 7
    packetPayloadBytes := 40962
    flowFrameBytes := 828505
    lowConfidenceResidue := 3
    checksumMismatchCount := 0
    auditGapCount := 0 }

def witnessMeasurement : GnosisRichnessMeasurement :=
  measureSyntheticGnosis 1000000 witnessWeights witnessVector

theorem witness_measurement_bounded : ScoreBounded witnessMeasurement := by
  unfold witnessMeasurement
  exact measured_score_bounded 1000000 witnessWeights witnessVector

theorem witness_measurement_observational :
    ObservationalMeasurement witnessMeasurement := by
  rfl

end SyntheticGnosisMeasurement
