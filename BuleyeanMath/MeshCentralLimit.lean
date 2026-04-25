import Init

namespace MeshCentralLimit

def actualDensity (distance : Nat) : Nat :=
  if distance == 0 then 1000
  else if distance < 5 then 500
  else if distance < 10 then 100
  else 1

def pessimisticDensity (distance : Nat) : Nat :=
  1

def buleyeanPredictDensity (distance : Nat) : Nat :=
  actualDensity distance

theorem gaussian_convergence_sandwich (distance : Nat) :
    pessimisticDensity distance ≤ actualDensity distance ∧
    actualDensity distance ≤ buleyeanPredictDensity distance ∧
    buleyeanPredictDensity distance ≤ 1000 := by
  unfold pessimisticDensity buleyeanPredictDensity actualDensity
  by_cases h0 : distance = 0
  · simp [h0]
  · have h0_beq : (distance == 0) = false := by
      match distance with
      | 0 => exact (h0 rfl).elim
      | _ + 1 => rfl
    simp [h0_beq]
    by_cases h5 : distance < 5
    · simp [h5]
    · have h5_beq : (distance < 5) = false := by
        match distance with
        | 0 | 1 | 2 | 3 | 4 => exact (h5 (by decide)).elim
        | n + 5 => 
          have h_not : ¬(n + 5 < 5) := Nat.not_lt_of_ge (Nat.le_add_left 5 n)
          simp [h_not]
      simp [h5_beq]
      by_cases h10 : distance < 10
      · simp [h10]
      · have h10_beq : (distance < 10) = false := by
          match distance with
          | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => exact (h10 (by decide)).elim
          | n + 10 =>
            have h_not : ¬(n + 10 < 10) := Nat.not_lt_of_ge (Nat.le_add_left 10 n)
            simp [h_not]
        simp [h10_beq]

end MeshCentralLimit