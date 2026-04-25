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
  unfold pessimisticConfidence foldingConfidence buleyeanPredictConfidence
  have h_ne_zero : (d == 0) = false := by
    match d with | 0 => exact (Nat.lt_irrefl 0 h).elim | _ + 1 => rfl
  simp [h_ne_zero]
  by_cases h_many : d > 10
  · simp [h_many]
    constructor
    · match d with
      | 0 => exact (Nat.lt_irrefl 0 h).elim
      | d' + 1 => 
        apply Nat.le_sub_of_add_le
        have h_ge_11 : d' + 1 >= 11 := h_many
        have h_div : 1000 / (d' + 1) <= 90 := by
          apply Nat.div_le_div_left h_ge_11 (by decide)
        apply Nat.le_trans (Nat.add_le_add_right h_div 500) (by decide)
    · constructor; apply Nat.le_refl; apply Nat.sub_le
  · simp [h_many]
    constructor; apply Nat.zero_le; constructor; apply Nat.le_refl; apply Nat.sub_le

end MeshTransientFolding
