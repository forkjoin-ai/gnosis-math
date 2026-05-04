import Init

namespace MeshContinuedFractions

def probTermGe (K : Nat) : Nat :=
  if K == 0 then 1000 else 1000 / K

def pessimisticProb (K : Nat) : Nat :=
  if K > 0 then 1 else 1000

def buleyeanPredictProb (K : Nat) : Nat :=
  probTermGe K

theorem gauss_kuzmin_sandwich (K : Nat) (hK : K ≤ 1000) :
    pessimisticProb K ≤ probTermGe K ∧
    probTermGe K ≤ buleyeanPredictProb K ∧
    buleyeanPredictProb K ≤ 1000 := by
  unfold pessimisticProb probTermGe buleyeanPredictProb
  match hK_val : K with
  | 0 => 
    simp
    decide
  | 1 => 
    simp
    decide
  | n + 2 =>
    have h_pos : 0 < n + 2 := Nat.succ_pos (n + 1)
    have h_not_zero : (n + 2 == 0) = false := by rfl
    simp [h_pos, h_not_zero]
    constructor
    · -- 1 ≤ 1000 / (n + 2)
      match h_div : 1000 / (n + 2) with
      | 0 =>
        have h_contra := Nat.div_eq_zero_iff.mp h_div
        -- h_contra : n + 2 = 0 ∨ 1000 < n + 2
        -- both impossible: n+2 ≠ 0 (succ), and n+2 ≤ 1000 from hK
        exact h_contra.elim
          (fun hZero => absurd hZero (Nat.succ_ne_zero (n + 1)))
          (fun hGt => absurd hK (Nat.not_le_of_lt hGt))
      | k + 1 => exact Nat.succ_le_succ (Nat.zero_le k)
    · constructor
      · apply Nat.le_refl
      · apply Nat.div_le_self



end MeshContinuedFractions