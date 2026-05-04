import Init

namespace MeshPiWhipsaw

def patternStrength (n : Nat) : Nat :=
  if n == 0 then 1000 else 1000 / n

def pessimisticPattern (n : Nat) : Nat :=
  if n > 1000 then 0 else 1

def buleyeanPredictPattern (n : Nat) : Nat :=
  patternStrength n

theorem digit_whipsaw_sandwich (n : Nat) (h : n >= 1) :
    pessimisticPattern n ≤ patternStrength n ∧
    patternStrength n ≤ buleyeanPredictPattern n ∧
    buleyeanPredictPattern n ≤ 1000 := by
  constructor
  · unfold pessimisticPattern patternStrength
    by_cases h1 : n > 1000
    · simp [h1]
    · have h_not_zero : (n == 0) = false := by 
        match n with | 0 => contradiction | _ + 1 => rfl
      simp [h1, h_not_zero]
      match h_div : 1000 / n with
      | 0 =>
        have h_contra := Nat.div_eq_zero_iff.mp h_div
        -- h_contra : n = 0 ∨ 1000 < n
        -- h : n ≥ 1 rules out n = 0; h1 : ¬ n > 1000 rules out 1000 < n
        exact h_contra.elim
          (fun hz => absurd (hz ▸ h) (by decide))
          (fun hgt => absurd hgt h1)
      | m + 1 => exact Nat.succ_pos m
  · constructor
    · unfold buleyeanPredictPattern; apply Nat.le_refl
    · unfold buleyeanPredictPattern patternStrength
      split
      · exact Nat.le_refl 1000
      · apply Nat.div_le_self

end MeshPiWhipsaw
