import Init

namespace MeshMemoryLeaks

def availableMemory (t leakRate : Nat) : Nat :=
  if 1000 < t * leakRate then 0
  else 1000 - (t * leakRate)

def pessimisticStability (t leakRate : Nat) : Nat :=
  if leakRate > 0 then 0 else 1000

def buleyeanPredictStability (t leakRate : Nat) : Nat :=
  availableMemory t leakRate

theorem oom_inevitability_sandwich (t leakRate : Nat) :
    pessimisticStability t leakRate ≤ availableMemory t leakRate ∧
    availableMemory t leakRate ≤ buleyeanPredictStability t leakRate ∧
    buleyeanPredictStability t leakRate ≤ 1000 := by
  unfold pessimisticStability availableMemory buleyeanPredictStability
  by_cases h_leak : leakRate > 0
  · simp [h_leak]
    constructor
    · apply Nat.zero_le
    · constructor; apply Nat.le_refl; apply Nat.sub_le
  · have h_zero : leakRate = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_gt h_leak)
    simp [h_zero]
    constructor; apply Nat.le_refl; constructor; apply Nat.le_refl; apply Nat.le_refl

end MeshMemoryLeaks