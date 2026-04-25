import Init

namespace MeshContinuedFractions

def probTermGe (K : Nat) : Nat :=
  if K == 0 then 1000 else 1000 / K

def pessimisticProb (K : Nat) : Nat :=
  if K > 0 then 1 else 1000

def buleyeanPredictProb (K : Nat) : Nat :=
  probTermGe K

theorem gauss_kuzmin_sandwich (K : Nat) :
    pessimisticProb K ≤ probTermGe K ∧
    probTermGe K ≤ buleyeanPredictProb K ∧
    buleyeanPredictProb K ≤ 1000 := by
  unfold pessimisticProb probTermGe buleyeanPredictProb
  by_cases h0 : K = 0
  · simp [h0]
  · have h0_beq : (K == 0) = false := by
      match K with | 0 => exact (h0 rfl).elim | _ + 1 => rfl
    simp [h0_beq]
    constructor
    · apply Nat.div_le_div_left
      match K with | 0 => exact (h0 rfl).elim | n + 1 => apply Nat.le_add_left
      match K with | 0 => exact (h0 rfl).elim | _ + 1 => decide
    · constructor; apply Nat.le_refl; apply Nat.div_le_self

end MeshContinuedFractions