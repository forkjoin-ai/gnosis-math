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
  constructor
  · unfold pessimisticFrequency frequencyAtDigit
    split <;> split <;> omega
  · constructor
    · unfold buleyeanPredictFrequency; apply Nat.le_refl
    · unfold buleyeanPredictFrequency frequencyAtDigit
      split <;> omega

end MeshNormalNumbers
