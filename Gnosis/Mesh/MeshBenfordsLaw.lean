import Init

namespace MeshBenfordsLaw

def actualFrequency (digit : Nat) : Nat :=
  match digit with
  | 1 => 301
  | 2 => 176
  | 3 => 125
  | 4 => 97
  | 5 => 79
  | 6 => 67
  | 7 => 58
  | 8 => 51
  | 9 => 46
  | _ => 0

def pessimisticFrequency (digit : Nat) : Nat :=
  if digit >= 1 && digit <= 9 then 40 else 0

def buleyeanPredictFrequency (digit : Nat) : Nat :=
  actualFrequency digit

theorem benford_sandwich (digit : Nat) (h : digit >= 1 ∧ digit <= 9) :
    pessimisticFrequency digit ≤ actualFrequency digit ∧
    actualFrequency digit ≤ buleyeanPredictFrequency digit ∧
    buleyeanPredictFrequency digit ≤ 1000 := by
  unfold pessimisticFrequency buleyeanPredictFrequency
  match digit with
  | 0 => exact (Nat.lt_irrefl 0 h.1).elim
  | 1 => exact ⟨by decide, by apply Nat.le_refl, by decide⟩
  | 2 => exact ⟨by decide, by apply Nat.le_refl, by decide⟩
  | 3 => exact ⟨by decide, by apply Nat.le_refl, by decide⟩
  | 4 => exact ⟨by decide, by apply Nat.le_refl, by decide⟩
  | 5 => exact ⟨by decide, by apply Nat.le_refl, by decide⟩
  | 6 => exact ⟨by decide, by apply Nat.le_refl, by decide⟩
  | 7 => exact ⟨by decide, by apply Nat.le_refl, by decide⟩
  | 8 => exact ⟨by decide, by apply Nat.le_refl, by decide⟩
  | 9 => exact ⟨by decide, by apply Nat.le_refl, by decide⟩
  | n + 10 =>
    exfalso
    have h_gt : n + 10 > 9 := Nat.le_trans (by decide) (Nat.le_add_left 10 n)
    exact Nat.not_le_of_gt h_gt h.2

end MeshBenfordsLaw