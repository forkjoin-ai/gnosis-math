import Init

namespace MeshTransientFolding

def foldingConfidence (d : Nat) : Nat :=
  if d == 0 then 0 else 1000 - (1000 / d)

def pessimisticConfidence (d : Nat) : Nat :=
  if d > 10 then 500 else 0

def buleyeanPredictConfidence (d : Nat) : Nat :=
  foldingConfidence d

theorem folding_sandwich (d : Nat) (h : d >= 1) :
    pessimisticConfidence d ≤ foldingConfidence d ∧
    foldingConfidence d ≤ buleyeanPredictConfidence d ∧
    buleyeanPredictConfidence d ≤ 1000 := by
  constructor
  · unfold pessimisticConfidence foldingConfidence
    by_cases h_many : d > 10
    · simp [h_many]
      split
      · omega
      · have h_ge_11 : 11 ≤ d := by omega
        have h_div : 1000 / d ≤ 90 := Nat.div_le_div_left h_ge_11 (by decide)
        apply Nat.le_trans (by decide : 500 ≤ 1000 - 90)
        exact Nat.sub_le_sub_left h_div 1000
    · simp [h_many]
  · constructor
    · unfold buleyeanPredictConfidence; apply Nat.le_refl
    · unfold buleyeanPredictConfidence foldingConfidence
      split
      · omega
      · apply Nat.sub_le

end MeshTransientFolding
