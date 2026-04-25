import Init

namespace MeshNormalNumbers

def frequencyAtDigit (digit n : Nat) : Nat :=
  if digit >= 10 then 0 else 100

def pessimisticFrequency (digit : Nat) : Nat :=
  if digit < 10 then 10 else 0

def buleyeanPredictFrequency (digit : Nat) : Nat :=
  frequencyAtDigit digit 1000

theorem normal_number_sandwich (digit : Nat) (h : digit < 10) :
    pessimisticFrequency digit ≤ frequencyAtDigit digit 1000 ∧
    frequencyAtDigit digit 1000 ≤ buleyeanPredictFrequency digit ∧
    buleyeanPredictFrequency digit ≤ 1000 := by
  unfold pessimisticFrequency frequencyAtDigit buleyeanPredictFrequency
  match h_digit : (digit < 10) with
  | true => 
    have h_not : (digit >= 10) = false := by
      simp [Nat.not_le_of_gt (by simp [h_digit])]
    simp [h_digit, h_not]
    constructor; decide; constructor; apply Nat.le_refl; decide
  | false => 
    have h_not : (digit < 10) = true := by simp [h]
    exact (Bool.noConfusion (h_not.symm.trans h_digit))

end MeshNormalNumbers
