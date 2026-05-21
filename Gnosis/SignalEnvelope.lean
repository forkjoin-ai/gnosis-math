import Init

namespace Gnosis
namespace SignalEnvelope

/-!
  SignalEnvelope is the formal boundary for Aeon Voting 4.0 market-as-signal
  runtime records. The runtime may cite these theorem names only for the
  structural facts proved here: estimates, confidence, freshness, and privacy
  budget are bounded fields, not truth claims.
-/

structure SignalEnvelope where
  estimate : Nat
  confidence : Nat
  freshness : Nat
  privacyBudget : Nat
  deriving Repr, DecidableEq

structure ReliabilityFactors where
  confidence : Nat
  freshness : Nat
  calibrationTrust : Nat
  privacyWeight : Nat
  sampleWeight : Nat
  deriving Repr, DecidableEq

def valid (s : SignalEnvelope) : Prop :=
  s.estimate ≤ 100 ∧ s.confidence ≤ 100 ∧ s.freshness ≤ 100 ∧ s.privacyBudget ≤ 100

def validReliabilityFactors (r : ReliabilityFactors) : Prop :=
  r.confidence ≤ 100 ∧
  r.freshness ≤ 100 ∧
  r.calibrationTrust ≤ 100 ∧
  r.privacyWeight ≤ 100 ∧
  r.sampleWeight ≤ 100

def reliabilityFactorsLe (low high : ReliabilityFactors) : Prop :=
  low.confidence ≤ high.confidence ∧
  low.freshness ≤ high.freshness ∧
  low.calibrationTrust ≤ high.calibrationTrust ∧
  low.privacyWeight ≤ high.privacyWeight ∧
  low.sampleWeight ≤ high.sampleWeight

def admissiblePrivacyWeight (s : SignalEnvelope) : Nat :=
  s.privacyBudget

def reliabilityNumerator (r : ReliabilityFactors) : Nat :=
  r.confidence * r.freshness * r.calibrationTrust * r.privacyWeight * r.sampleWeight

def admissibleReliabilityWeight (r : ReliabilityFactors) : Nat :=
  reliabilityNumerator r / (100 * 100 * 100 * 100)

def withPrivacyBudget (s : SignalEnvelope) (privacyBudget : Nat) : SignalEnvelope :=
  { s with privacyBudget := privacyBudget }

theorem valid_estimate_bounded (s : SignalEnvelope) (h : valid s) :
    s.estimate ≤ 100 := h.left

theorem valid_confidence_bounded (s : SignalEnvelope) (h : valid s) :
    s.confidence ≤ 100 := h.right.left

theorem valid_freshness_bounded (s : SignalEnvelope) (h : valid s) :
    s.freshness ≤ 100 := h.right.right.left

theorem valid_privacy_budget_bounded (s : SignalEnvelope) (h : valid s) :
    s.privacyBudget ≤ 100 := h.right.right.right

theorem admissible_privacy_weight_bounded (s : SignalEnvelope) (h : valid s) :
    admissiblePrivacyWeight s ≤ 100 := valid_privacy_budget_bounded s h

theorem lower_privacy_budget_no_more_admissible_weight
    (s : SignalEnvelope) (lowerBudget : Nat)
    (hLower : lowerBudget ≤ s.privacyBudget) :
    admissiblePrivacyWeight (withPrivacyBudget s lowerBudget) ≤
      admissiblePrivacyWeight s := by
  dsimp [admissiblePrivacyWeight, withPrivacyBudget]
  exact hLower

theorem lower_valid_privacy_budget_preserves_valid
    (s : SignalEnvelope) (hValid : valid s)
    (lowerBudget : Nat) (hLower : lowerBudget ≤ s.privacyBudget) :
    valid (withPrivacyBudget s lowerBudget) := by
  dsimp [valid, withPrivacyBudget]
  exact ⟨hValid.left, hValid.right.left, hValid.right.right.left,
    Nat.le_trans hLower hValid.right.right.right⟩

theorem reliability_numerator_bounded
    (r : ReliabilityFactors) (h : validReliabilityFactors r) :
    reliabilityNumerator r ≤ 100 * 100 * 100 * 100 * 100 := by
  dsimp [validReliabilityFactors] at h
  dsimp [reliabilityNumerator]
  exact Nat.mul_le_mul
    (Nat.mul_le_mul
      (Nat.mul_le_mul
        (Nat.mul_le_mul h.left h.right.left)
        h.right.right.left)
      h.right.right.right.left)
    h.right.right.right.right

theorem admissible_reliability_weight_bounded
    (r : ReliabilityFactors) (h : validReliabilityFactors r) :
    admissibleReliabilityWeight r ≤ 100 := by
  dsimp [admissibleReliabilityWeight]
  have hNumerator :
      reliabilityNumerator r ≤ 100 * (100 * 100 * 100 * 100) := by
    calc
      reliabilityNumerator r ≤ 100 * 100 * 100 * 100 * 100 :=
        reliability_numerator_bounded r h
      _ = 100 * (100 * 100 * 100 * 100) := by
        rfl
  exact Nat.div_le_of_le_mul (by
    rw [Nat.mul_comm]
    exact hNumerator)

def reliabilityWithFreshness
    (confidence freshness calibrationTrust privacyWeight sampleWeight : Nat) :
    ReliabilityFactors :=
  {
    confidence := confidence
    freshness := freshness
    calibrationTrust := calibrationTrust
    privacyWeight := privacyWeight
    sampleWeight := sampleWeight
  }

theorem reliability_numerator_no_more_after_freshness_decrease
    (confidence lowFreshness highFreshness calibrationTrust privacyWeight sampleWeight : Nat)
    (hFreshness : lowFreshness ≤ highFreshness) :
    reliabilityNumerator
        (reliabilityWithFreshness confidence lowFreshness calibrationTrust privacyWeight sampleWeight)
      ≤
      reliabilityNumerator
        (reliabilityWithFreshness confidence highFreshness calibrationTrust privacyWeight sampleWeight) := by
  dsimp [reliabilityWithFreshness, reliabilityNumerator]
  exact Nat.mul_le_mul_right sampleWeight
    (Nat.mul_le_mul_right privacyWeight
      (Nat.mul_le_mul_right calibrationTrust
        (Nat.mul_le_mul_left confidence hFreshness)))

theorem admissible_reliability_no_more_after_freshness_decrease
    (confidence lowFreshness highFreshness calibrationTrust privacyWeight sampleWeight : Nat)
    (hFreshness : lowFreshness ≤ highFreshness) :
    admissibleReliabilityWeight
        (reliabilityWithFreshness confidence lowFreshness calibrationTrust privacyWeight sampleWeight)
      ≤
      admissibleReliabilityWeight
        (reliabilityWithFreshness confidence highFreshness calibrationTrust privacyWeight sampleWeight) := by
  dsimp [admissibleReliabilityWeight]
  exact Nat.div_le_div_right
    (reliability_numerator_no_more_after_freshness_decrease
      confidence lowFreshness highFreshness calibrationTrust privacyWeight sampleWeight hFreshness)

def reliabilityWithPrivacyWeight
    (confidence freshness calibrationTrust privacyWeight sampleWeight : Nat) :
    ReliabilityFactors :=
  {
    confidence := confidence
    freshness := freshness
    calibrationTrust := calibrationTrust
    privacyWeight := privacyWeight
    sampleWeight := sampleWeight
  }

theorem reliability_numerator_no_more_after_privacy_weight_decrease
    (confidence freshness calibrationTrust lowPrivacy highPrivacy sampleWeight : Nat)
    (hPrivacy : lowPrivacy ≤ highPrivacy) :
    reliabilityNumerator
        (reliabilityWithPrivacyWeight confidence freshness calibrationTrust lowPrivacy sampleWeight)
      ≤
      reliabilityNumerator
        (reliabilityWithPrivacyWeight confidence freshness calibrationTrust highPrivacy sampleWeight) := by
  dsimp [reliabilityWithPrivacyWeight, reliabilityNumerator]
  exact Nat.mul_le_mul_right sampleWeight
    (Nat.mul_le_mul_left (confidence * freshness * calibrationTrust) hPrivacy)

theorem admissible_reliability_no_more_after_privacy_weight_decrease
    (confidence freshness calibrationTrust lowPrivacy highPrivacy sampleWeight : Nat)
    (hPrivacy : lowPrivacy ≤ highPrivacy) :
    admissibleReliabilityWeight
        (reliabilityWithPrivacyWeight confidence freshness calibrationTrust lowPrivacy sampleWeight)
      ≤
      admissibleReliabilityWeight
        (reliabilityWithPrivacyWeight confidence freshness calibrationTrust highPrivacy sampleWeight) := by
  dsimp [admissibleReliabilityWeight]
  exact Nat.div_le_div_right
    (reliability_numerator_no_more_after_privacy_weight_decrease
      confidence freshness calibrationTrust lowPrivacy highPrivacy sampleWeight hPrivacy)

def reliabilityWithSampleWeight
    (confidence freshness calibrationTrust privacyWeight sampleWeight : Nat) :
    ReliabilityFactors :=
  {
    confidence := confidence
    freshness := freshness
    calibrationTrust := calibrationTrust
    privacyWeight := privacyWeight
    sampleWeight := sampleWeight
  }

theorem reliability_numerator_no_more_after_sample_weight_increase
    (confidence freshness calibrationTrust privacyWeight lowSample highSample : Nat)
    (hSample : lowSample ≤ highSample) :
    reliabilityNumerator
        (reliabilityWithSampleWeight confidence freshness calibrationTrust privacyWeight lowSample)
      ≤
      reliabilityNumerator
        (reliabilityWithSampleWeight confidence freshness calibrationTrust privacyWeight highSample) := by
  dsimp [reliabilityWithSampleWeight, reliabilityNumerator]
  exact Nat.mul_le_mul_left (confidence * freshness * calibrationTrust * privacyWeight) hSample

theorem admissible_reliability_no_more_after_sample_weight_increase
    (confidence freshness calibrationTrust privacyWeight lowSample highSample : Nat)
    (hSample : lowSample ≤ highSample) :
    admissibleReliabilityWeight
        (reliabilityWithSampleWeight confidence freshness calibrationTrust privacyWeight lowSample)
      ≤
      admissibleReliabilityWeight
        (reliabilityWithSampleWeight confidence freshness calibrationTrust privacyWeight highSample) := by
  dsimp [admissibleReliabilityWeight]
  exact Nat.div_le_div_right
    (reliability_numerator_no_more_after_sample_weight_increase
      confidence freshness calibrationTrust privacyWeight lowSample highSample hSample)

def reliabilityWithConfidence
    (confidence freshness calibrationTrust privacyWeight sampleWeight : Nat) :
    ReliabilityFactors :=
  {
    confidence := confidence
    freshness := freshness
    calibrationTrust := calibrationTrust
    privacyWeight := privacyWeight
    sampleWeight := sampleWeight
  }

theorem reliability_numerator_no_more_after_confidence_increase
    (lowConfidence highConfidence freshness calibrationTrust privacyWeight sampleWeight : Nat)
    (hConfidence : lowConfidence ≤ highConfidence) :
    reliabilityNumerator
        (reliabilityWithConfidence lowConfidence freshness calibrationTrust privacyWeight sampleWeight)
      ≤
      reliabilityNumerator
        (reliabilityWithConfidence highConfidence freshness calibrationTrust privacyWeight sampleWeight) := by
  dsimp [reliabilityWithConfidence, reliabilityNumerator]
  exact Nat.mul_le_mul_right sampleWeight
    (Nat.mul_le_mul_right privacyWeight
      (Nat.mul_le_mul_right calibrationTrust
        (Nat.mul_le_mul_right freshness hConfidence)))

theorem admissible_reliability_no_more_after_confidence_increase
    (lowConfidence highConfidence freshness calibrationTrust privacyWeight sampleWeight : Nat)
    (hConfidence : lowConfidence ≤ highConfidence) :
    admissibleReliabilityWeight
        (reliabilityWithConfidence lowConfidence freshness calibrationTrust privacyWeight sampleWeight)
      ≤
      admissibleReliabilityWeight
        (reliabilityWithConfidence highConfidence freshness calibrationTrust privacyWeight sampleWeight) := by
  dsimp [admissibleReliabilityWeight]
  exact Nat.div_le_div_right
    (reliability_numerator_no_more_after_confidence_increase
      lowConfidence highConfidence freshness calibrationTrust privacyWeight sampleWeight hConfidence)

theorem reliability_numerator_monotone
    (low high : ReliabilityFactors)
    (h : reliabilityFactorsLe low high) :
    reliabilityNumerator low ≤ reliabilityNumerator high := by
  dsimp [reliabilityFactorsLe] at h
  dsimp [reliabilityNumerator]
  exact Nat.mul_le_mul
    (Nat.mul_le_mul
      (Nat.mul_le_mul
        (Nat.mul_le_mul h.left h.right.left)
        h.right.right.left)
      h.right.right.right.left)
    h.right.right.right.right

theorem admissible_reliability_weight_monotone
    (low high : ReliabilityFactors)
    (h : reliabilityFactorsLe low high) :
    admissibleReliabilityWeight low ≤ admissibleReliabilityWeight high := by
  dsimp [admissibleReliabilityWeight]
  exact Nat.div_le_div_right (reliability_numerator_monotone low high h)

end SignalEnvelope
end Gnosis
