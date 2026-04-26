import Init

namespace MeshInfiniteMonkeys

def pShakespeare (t : Nat) : Nat :=
  if t == 0 then 0 else 1000 - (1000 / t)

def pessimisticReachability (t : Nat) : Nat :=
  if t > 0 then 1 else 0

def buleyeanPredictReachability (t : Nat) : Nat :=
  pShakespeare t

theorem monkey_sandwich (t : Nat) (h : t >= 1) :
    pessimisticReachability t ≤ pShakespeare t ∧
    pShakespeare t ≤ buleyeanPredictReachability t ∧
    buleyeanPredictReachability t ≤ 1000 := by
  unfold pessimisticReachability pShakespeare buleyeanPredictReachability
  match ht_val : t with
  | 0 => 
    simp [ht_val]
    decide
  | 1 => 
    simp [ht_val]
    decide
  | n + 2 => 
    have h_not_zero : (t == 0) = false := by simp [ht_val]
    simp [h_not_zero]
    constructor
    · -- 1 ≤ 1000 - 1000 / t
      match h_div : 1000 / t with
      | 0 => 
        have h_contra := Nat.div_eq_zero_iff.mp h_div
        omega
      | m + 1 => omega
    · constructor
      · apply Nat.le_refl
      · apply Nat.sub_le






























































































































































































end MeshInfiniteMonkeys