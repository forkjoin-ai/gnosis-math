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
  unfold pessimisticPattern patternStrength buleyeanPredictPattern
  have h_ne_zero : (n == 0) = false := by
    match n with | 0 => exact (Nat.lt_irrefl 0 h).elim | _ + 1 => rfl
  simp [h_ne_zero]
  by_cases h_large : n > 1000
  · simp [h_large]
  · simp [h_large]
    constructor
    · match n with
      | 0 => exact (Nat.lt_irrefl 0 h).elim
      | 1 => decide
      | n' + 2 => decide
    · constructor; apply Nat.le_refl; apply Nat.div_le_self

end MeshPiWhipsaw
