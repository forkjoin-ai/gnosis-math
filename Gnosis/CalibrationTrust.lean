import Init
import Gnosis.SignalEnvelope

namespace Gnosis
namespace CalibrationTrust

open Gnosis.SignalEnvelope

def trustAfterResidual (prior residual : Nat) : Nat :=
  prior - residual

structure TrustObservation where
  prior : Nat
  residual : Nat
  deriving Repr, DecidableEq

def observationTrust (o : TrustObservation) : Nat :=
  trustAfterResidual o.prior o.residual

def totalTrust : List TrustObservation → Nat
  | [] => 0
  | observation :: rest => observationTrust observation + totalTrust rest

def residualsIncrease : List TrustObservation → List TrustObservation → Prop
  | [], [] => True
  | before :: beforeRest, after :: afterRest =>
      before.prior = after.prior ∧
      before.residual ≤ after.residual ∧
      residualsIncrease beforeRest afterRest
  | _, _ => False

theorem trust_never_exceeds_prior (prior residual : Nat) :
    trustAfterResidual prior residual ≤ prior := by
  exact Nat.sub_le prior residual

theorem zero_residual_preserves_trust (prior : Nat) :
    trustAfterResidual prior 0 = prior := by
  simp [trustAfterResidual]

theorem larger_residual_no_more_trust (prior small large : Nat)
    (h : small ≤ large) :
    trustAfterResidual prior large ≤ trustAfterResidual prior small := by
  exact Nat.sub_le_sub_left h prior

theorem observation_trust_no_more_after_residual_increase
    (before after : TrustObservation)
    (hPrior : before.prior = after.prior)
    (hResidual : before.residual ≤ after.residual) :
    observationTrust after ≤ observationTrust before := by
  dsimp [observationTrust, trustAfterResidual]
  rw [← hPrior]
  exact larger_residual_no_more_trust before.prior before.residual after.residual hResidual

theorem total_trust_no_more_after_residual_increase
    (before after : List TrustObservation)
    (h : residualsIncrease before after) :
    totalTrust after ≤ totalTrust before := by
  induction before generalizing after with
  | nil =>
      cases after with
      | nil =>
          simp [totalTrust]
      | cons _ _ =>
          contradiction
  | cons beforeHead beforeRest ih =>
      cases after with
      | nil =>
          contradiction
      | cons afterHead afterRest =>
          dsimp [residualsIncrease] at h
          dsimp [totalTrust]
          exact Nat.add_le_add
            (observation_trust_no_more_after_residual_increase
              beforeHead afterHead h.left h.right.left)
            (ih afterRest h.right.right)

def reliabilityFromResidual
    (confidence freshness prior residual privacyWeight sampleWeight : Nat) :
    ReliabilityFactors :=
  {
    confidence := confidence
    freshness := freshness
    calibrationTrust := trustAfterResidual prior residual
    privacyWeight := privacyWeight
    sampleWeight := sampleWeight
  }

theorem reliability_numerator_no_more_after_residual_increase
    (confidence freshness prior smallResidual largeResidual privacyWeight sampleWeight : Nat)
    (hResidual : smallResidual ≤ largeResidual) :
    reliabilityNumerator
        (reliabilityFromResidual confidence freshness prior largeResidual privacyWeight sampleWeight)
      ≤
      reliabilityNumerator
        (reliabilityFromResidual confidence freshness prior smallResidual privacyWeight sampleWeight) := by
  dsimp [reliabilityFromResidual, reliabilityNumerator]
  exact Nat.mul_le_mul_right sampleWeight
    (Nat.mul_le_mul_right privacyWeight
      (Nat.mul_le_mul_left (confidence * freshness)
        (larger_residual_no_more_trust prior smallResidual largeResidual hResidual)))

theorem admissible_reliability_no_more_after_residual_increase
    (confidence freshness prior smallResidual largeResidual privacyWeight sampleWeight : Nat)
    (hResidual : smallResidual ≤ largeResidual) :
    admissibleReliabilityWeight
        (reliabilityFromResidual confidence freshness prior largeResidual privacyWeight sampleWeight)
      ≤
      admissibleReliabilityWeight
        (reliabilityFromResidual confidence freshness prior smallResidual privacyWeight sampleWeight) := by
  dsimp [admissibleReliabilityWeight]
  exact Nat.div_le_div_right
    (reliability_numerator_no_more_after_residual_increase
      confidence freshness prior smallResidual largeResidual privacyWeight sampleWeight hResidual)

end CalibrationTrust
end Gnosis
