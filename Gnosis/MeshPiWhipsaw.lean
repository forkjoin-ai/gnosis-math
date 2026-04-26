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
    · simp [h1]; apply Nat.zero_le
    · have h_not_zero : (n == 0) = false := by 
        match n with | 0 => contradiction | _ + 1 => rfl
      simp [h1, h_not_zero]
      match h_div : 1000 / n with
      | 0 => 
        have h_contra := Nat.div_eq_zero_iff.mp h_div
        omega
      | m + 1 => omega
  · constructor
    · unfold buleyeanPredictPattern; apply Nat.le_refl
    · unfold buleyeanPredictPattern patternStrength
      split
      · omega
      · apply Nat.div_le_self

end MeshPiWhipsaw
