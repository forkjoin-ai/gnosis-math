import Init

namespace MeshInfiniteMonkeys

def pShakespeare (t : Nat) : Nat :=
  if t == 0 then 0 else 1000 - (1000 / t)

def pessimisticReachability (t : Nat) : Nat :=
  if t > 1 then 1 else 0

def buleyeanPredictReachability (t : Nat) : Nat :=
  pShakespeare t

theorem monkey_sandwich (t : Nat) (h : t >= 1) :
    pessimisticReachability t ≤ pShakespeare t ∧
    pShakespeare t ≤ buleyeanPredictReachability t ∧
    buleyeanPredictReachability t ≤ 1000 := by
  constructor
  · unfold pessimisticReachability pShakespeare
    by_cases h1 : t > 1
    · simp [h1]
      split
      · rename_i ht0
        exact absurd (ht0 ▸ h1) (Nat.not_lt_zero 1)
      · -- h1 : t > 1 is definitionally 2 ≤ t in Lean 4 Nat
        have h_ge_2 : 2 ≤ t := h1
        have h_div_val : 1000 / t ≤ 500 := Nat.div_le_div_left h_ge_2 (by decide)
        apply Nat.le_trans (by decide : 1 ≤ 1000 - 500)
        exact Nat.sub_le_sub_left h_div_val 1000
    · have h_le_1 : t ≤ 1 := Nat.le_of_not_gt h1
      have h1_eq : t = 1 := Nat.le_antisymm h_le_1 h
      simp [h1_eq]
  constructor
  · unfold buleyeanPredictReachability; apply Nat.le_refl
  · unfold buleyeanPredictReachability pShakespeare
    split
    · exact Nat.zero_le 1000
    · apply Nat.sub_le


















































































































































































































end MeshInfiniteMonkeys
