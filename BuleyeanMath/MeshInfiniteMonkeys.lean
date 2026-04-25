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
  have h_ne_zero : (t == 0) = false := by
    match t with | 0 => exact (Nat.lt_irrefl 0 h).elim | _ + 1 => rfl
  simp [h_ne_zero]
  constructor
  · match t with
    | 1 => decide
    | t' + 2 =>
      have h_div : 1000 / (t' + 2) ≤ 500 := by
        apply Nat.div_le_div_left; decide; decide
      have h_sub : 1000 - (1000 / (t' + 2)) ≥ 500 := Nat.le_sub_of_add_le (Nat.le_trans (Nat.add_le_add_right h_div 500) (by decide))
      exact Nat.le_trans (by decide) h_sub
  · constructor
    · apply Nat.le_refl
    · apply Nat.sub_le

end MeshInfiniteMonkeys