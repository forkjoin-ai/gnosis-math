import Init
import Gnosis.SignalEnvelope

namespace Gnosis
namespace SignalFusion

open Gnosis.SignalEnvelope

structure WeightedSignal where
  envelope : SignalEnvelope
  weight : Nat
  deriving Repr, DecidableEq

def validWeighted (s : WeightedSignal) : Prop :=
  SignalEnvelope.valid s.envelope ∧ s.weight ≤ 100

def contribution (s : WeightedSignal) : Nat :=
  s.envelope.estimate * s.weight

def normalizedFusion (weightedEstimate totalWeight : Nat) : Nat :=
  weightedEstimate / totalWeight

def totalContribution : List WeightedSignal → Nat
  | [] => 0
  | signal :: rest => contribution signal + totalContribution rest

def totalWeight : List WeightedSignal → Nat
  | [] => 0
  | signal :: rest => signal.weight + totalWeight rest

def allValidWeighted : List WeightedSignal → Prop
  | [] => True
  | signal :: rest => validWeighted signal ∧ allValidWeighted rest

theorem valid_weight_bounded (s : WeightedSignal) (h : validWeighted s) :
    s.weight ≤ 100 := h.right

theorem valid_contribution_bounded (s : WeightedSignal) (h : validWeighted s) :
    contribution s ≤ 10000 := by
  dsimp [contribution]
  exact Nat.mul_le_mul (SignalEnvelope.valid_estimate_bounded s.envelope h.left) h.right

theorem normalized_fusion_bounded
    (weightedEstimate totalWeight : Nat)
    (_hWeight : 0 < totalWeight)
    (hWeighted : weightedEstimate ≤ 100 * totalWeight) :
    normalizedFusion weightedEstimate totalWeight ≤ 100 := by
  dsimp [normalizedFusion]
  rw [Nat.mul_comm] at hWeighted
  exact Nat.div_le_of_le_mul hWeighted

theorem contribution_le_scaled_weight
    (signal : WeightedSignal) (h : validWeighted signal) :
    contribution signal ≤ 100 * signal.weight := by
  dsimp [contribution]
  exact Nat.mul_le_mul_right signal.weight
    (SignalEnvelope.valid_estimate_bounded signal.envelope h.left)

theorem contribution_monotone_in_weight
    (envelope : SignalEnvelope) (lowWeight highWeight : Nat)
    (hWeight : lowWeight ≤ highWeight) :
    contribution { envelope := envelope, weight := lowWeight } ≤
      contribution { envelope := envelope, weight := highWeight } := by
  dsimp [contribution]
  exact Nat.mul_le_mul_left envelope.estimate hWeight

theorem contribution_no_more_after_weight_decrease
    (envelope : SignalEnvelope) (lowWeight highWeight : Nat)
    (hWeight : lowWeight ≤ highWeight) :
    contribution { envelope := envelope, weight := lowWeight } ≤
      contribution { envelope := envelope, weight := highWeight } :=
  contribution_monotone_in_weight envelope lowWeight highWeight hWeight

def sourceInfluenceNumerator (sourceWeight : Nat) : Nat :=
  sourceWeight

def sourceInfluenceDenominator (otherWeight sourceWeight : Nat) : Nat :=
  otherWeight + sourceWeight

theorem normalized_source_share_no_more_after_weight_decrease
    (otherWeight lowWeight highWeight : Nat)
    (hWeight : lowWeight ≤ highWeight) :
    sourceInfluenceNumerator lowWeight * sourceInfluenceDenominator otherWeight highWeight ≤
      sourceInfluenceNumerator highWeight * sourceInfluenceDenominator otherWeight lowWeight := by
  dsimp [sourceInfluenceNumerator, sourceInfluenceDenominator]
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm lowWeight highWeight]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right otherWeight hWeight) (highWeight * lowWeight)

theorem added_source_above_baseline_pulls_fusion_up_cross
    (baseContribution baseWeight sourceEstimate sourceWeight : Nat)
    (hAbove : baseContribution ≤ sourceEstimate * baseWeight) :
    baseContribution * (baseWeight + sourceWeight) ≤
      (baseContribution + sourceEstimate * sourceWeight) * baseWeight := by
  rw [Nat.mul_add, Nat.add_mul]
  apply Nat.add_le_add_left
  calc
    baseContribution * sourceWeight
        ≤ (sourceEstimate * baseWeight) * sourceWeight :=
          Nat.mul_le_mul_right sourceWeight hAbove
    _ = sourceEstimate * sourceWeight * baseWeight := by
          rw [Nat.mul_assoc, Nat.mul_comm baseWeight sourceWeight, ← Nat.mul_assoc]

theorem added_source_below_baseline_pulls_fusion_down_cross
    (baseContribution baseWeight sourceEstimate sourceWeight : Nat)
    (hBelow : sourceEstimate * baseWeight ≤ baseContribution) :
    (baseContribution + sourceEstimate * sourceWeight) * baseWeight ≤
      baseContribution * (baseWeight + sourceWeight) := by
  rw [Nat.mul_add, Nat.add_mul]
  apply Nat.add_le_add_left
  calc
    sourceEstimate * sourceWeight * baseWeight
        = (sourceEstimate * baseWeight) * sourceWeight := by
          rw [Nat.mul_assoc, Nat.mul_comm sourceWeight baseWeight, ← Nat.mul_assoc]
    _ ≤ baseContribution * sourceWeight :=
          Nat.mul_le_mul_right sourceWeight hBelow

theorem added_source_between_baseline_and_bound_keeps_fusion_between
    (baseContribution baseWeight sourceEstimate sourceWeight upperBound : Nat)
    (hBaseBound : baseContribution ≤ upperBound * baseWeight)
    (hSourceBound : sourceEstimate ≤ upperBound) :
    baseContribution + sourceEstimate * sourceWeight ≤
      upperBound * (baseWeight + sourceWeight) := by
  rw [Nat.mul_add]
  exact Nat.add_le_add hBaseBound (Nat.mul_le_mul_right sourceWeight hSourceBound)

theorem total_contribution_le_scaled_total_weight
    (signals : List WeightedSignal)
    (h : allValidWeighted signals) :
    totalContribution signals ≤ 100 * totalWeight signals := by
  induction signals with
  | nil =>
      simp [totalContribution, totalWeight]
  | cons signal rest ih =>
      dsimp [allValidWeighted] at h
      dsimp [totalContribution, totalWeight]
      calc
        contribution signal + totalContribution rest
            ≤ 100 * signal.weight + 100 * totalWeight rest :=
              Nat.add_le_add
                (contribution_le_scaled_weight signal h.left)
                (ih h.right)
        _ = 100 * (signal.weight + totalWeight rest) := by
              rw [Nat.mul_add]

theorem normalized_fusion_of_valid_signals_bounded
    (signals : List WeightedSignal)
    (hValid : allValidWeighted signals)
    (hWeight : 0 < totalWeight signals) :
    normalizedFusion (totalContribution signals) (totalWeight signals) ≤ 100 :=
  normalized_fusion_bounded
    (totalContribution signals)
    (totalWeight signals)
    hWeight
    (total_contribution_le_scaled_total_weight signals hValid)

theorem source_separation_preserves_left (left right : WeightedSignal) :
    (left, right).fst = left := rfl

theorem source_separation_preserves_right (left right : WeightedSignal) :
    (left, right).snd = right := rfl

end SignalFusion
end Gnosis
