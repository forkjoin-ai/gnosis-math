import Init


namespace MeshMemoryLeaks

def availableMemory (t leakRate : Nat) : Nat :=
  if 1000 < t * leakRate then 0
  else 1000 - (t * leakRate)

def pessimisticStability (_t leakRate : Nat) : Nat :=
  if leakRate > 0 then 0 else 1000

def buleyeanPredictStability (t leakRate : Nat) : Nat :=
  availableMemory t leakRate

theorem oom_inevitability_sandwich (t leakRate : Nat) :
    pessimisticStability t leakRate ≤ availableMemory t leakRate ∧
    availableMemory t leakRate ≤ buleyeanPredictStability t leakRate ∧
    buleyeanPredictStability t leakRate ≤ 1000 := by
  constructor
  · unfold pessimisticStability availableMemory
    by_cases h : leakRate > 0
    · simp [h]
    · have h_zero : leakRate = 0 := by omega
      simp [h_zero]
  · constructor
    · unfold buleyeanPredictStability; apply Nat.le_refl
    · unfold buleyeanPredictStability availableMemory
      split <;> omega

end MeshMemoryLeaks