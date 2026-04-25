import Init

namespace MeshPiTopology

def unknowability (n : Nat) : Nat :=
  if n == 0 then 1000 else 1000 / n

def pessimisticLimit (n : Nat) : Nat :=
  if n > 1000 then 0 else 1

def buleyeanLimit (n : Nat) : Nat :=
  unknowability n

theorem pi_unknowable_sandwich (n : Nat) (h : n >= 1) :
    pessimisticLimit n ≤ unknowability n ∧
    unknowability n ≤ buleyeanLimit n ∧
    buleyeanLimit n ≤ 1000 := by
  unfold pessimisticLimit unknowability buleyeanLimit
  have h_ne_zero : (n == 0) = false := by
    match n with | 0 => exact (Nat.lt_irrefl 0 h).elim | _ + 1 => rfl
  simp [h_ne_zero]
  by_cases h_large : n > 1000
  · simp [h_large]
    exact ⟨Nat.zero_le _, Nat.le_refl _, Nat.div_le_self _ _⟩
  · simp [h_large]
    have h_le_1000 : n ≤ 1000 := Nat.le_of_not_gt h_large
    have h_div_ge_1 : 1000 / n ≥ 1 := by
      apply Nat.le_div_of_mul_le h
      exact h_le_1000
    exact ⟨h_div_ge_1, Nat.le_refl _, Nat.div_le_self _ _⟩

end MeshPiTopology
