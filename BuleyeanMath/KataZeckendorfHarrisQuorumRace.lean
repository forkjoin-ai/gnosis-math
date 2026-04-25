import BuleyeanMath.KataZeckendorfHarrisQuorumBridge
import BuleyeanMath.ZeckendorfCompleteness

namespace BuleyeanMath

open KataZeckendorfHarrisQuorumBridge

/-!
Init-only Kata-Zeckendorf-Harris quorum race.

Reuses the `Nat`-typed structures defined in the Bridge module
(`MultiLevelHarrisWitnessNat`, `GeometricErgodicityRateNat`,
`QueueBoundaryWitnessNat`, `kataZeckendorfBudget`).
-/

theorem kata_zeckendorf_gap_hypothesis_from_source :
    ZeckendorfCompleteness.fib 2 + ZeckendorfCompleteness.fib 3 ≤
      kataZeckendorfBudget := by
  decide

theorem kata_zeckendorf_budget_yields_multilevel_harris_witness_from_gap
    (_hGap :
      ZeckendorfCompleteness.fib 2 + ZeckendorfCompleteness.fib 3 ≤
        kataZeckendorfBudget) :
    ∃ witness : MultiLevelHarrisWitnessNat,
      witness.levels = 2 ∧
      witness.discreteDriftGap = kataZeckendorfBudget ∧
      witness.continuousDriftGap = kataZeckendorfBudget + 1 := by
  refine ⟨{
    levels := 2
    discreteDriftGap := kataZeckendorfBudget
    continuousDriftGap := kataZeckendorfBudget + 1
    hDiscrete := kataZeckendorfBudget_pos
    hContinuous := Nat.succ_pos _
  }, rfl, rfl, rfl⟩

theorem kata_zeckendorf_budget_yields_multilevel_harris_witness_via_gap :
    ∃ witness : MultiLevelHarrisWitnessNat,
      witness.levels = 2 ∧
      witness.discreteDriftGap = kataZeckendorfBudget ∧
      witness.continuousDriftGap = kataZeckendorfBudget + 1 :=
  kata_zeckendorf_budget_yields_multilevel_harris_witness_from_gap
    kata_zeckendorf_gap_hypothesis_from_source

theorem kata_zeckendorf_adapter_rate_subunit
    (rate : GeometricErgodicityRateNat) :
    rate.numerator < rate.denominator :=
  rate.hRateLtOne

theorem kata_zeckendorf_budget_majority_rate_embedding_yields_unit_boundary
    {replicaCount : Nat}
    (hReplica : replicaCount = 2 * kataZeckendorfBudget + 1) :
    kataZeckendorfBudget < quorumSize replicaCount kataZeckendorfBudget ∧
    ∃ boundary : QueueBoundaryWitnessNat,
      boundary.beta1 = 0 ∧
      boundary.capacity = 1 ∧
      boundary.occupancy = boundary.arrivalRate * boundary.residenceTime :=
  kata_zeckendorf_quorum_embedding_yields_unit_boundary hReplica

theorem kata_zeckendorf_budget_does_not_force_subunit_residence_time :
    ¬ (∀ boundary : QueueBoundaryWitnessNat,
      boundary.arrivalRate = kataZeckendorfBudget →
      boundary.serviceRate = kataZeckendorfBudget + 1 →
      boundary.residenceTime < 1) := by
  intro hSubunit
  let boundary : QueueBoundaryWitnessNat :=
    { beta1 := 0
      capacity := 1
      arrivalRate := kataZeckendorfBudget
      serviceRate := kataZeckendorfBudget + 1
      occupancy := kataZeckendorfBudget
      residenceTime := 1 }
  have hLt : boundary.residenceTime < 1 := hSubunit boundary rfl rfl
  exact Nat.lt_irrefl 1 hLt

end BuleyeanMath
