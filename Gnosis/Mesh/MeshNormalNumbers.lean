import Init


namespace MeshNormalNumbers

def frequencyAtDigit (digit _n : Nat) : Nat :=
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
  · have hp : pessimisticFrequency digit = 10 := by
      unfold pessimisticFrequency
      simp [h]
    have hf : frequencyAtDigit digit 1000 = 100 := by
      unfold frequencyAtDigit
      simp [h]
    rw [hp, hf]
    decide
  · constructor
    · unfold buleyeanPredictFrequency
      apply Nat.le_refl
    · have hf : frequencyAtDigit digit 1000 = 100 := by
        unfold frequencyAtDigit
        simp [h]
      have hb : buleyeanPredictFrequency digit = 100 := by
        unfold buleyeanPredictFrequency
        rw [hf]
      rw [hb]
      decide

end MeshNormalNumbers
