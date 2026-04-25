import Init

namespace MeshCollatzConjecture

def pessimisticStability (n : Nat) : Nat :=
  if n > 0 then 1 else 0

def buleyeanPredictStability (n : Nat) : Nat :=
  if n == 1 || n == 2 || n == 4 then 1000 else 1

def collatzStep (n : Nat) : Nat :=
  if n % 2 == 0 then n / 2 else 3 * n + 1

theorem collatz_1_2_4_cycle (n : Nat) (h : n = 1 ∨ n = 2 ∨ n = 4) :
    collatzStep n = 1 ∨ collatzStep n = 2 ∨ collatzStep n = 4 := by
  unfold collatzStep
  cases h with
  | inl h1 =>
    subst h1
    decide
  | inr h_rest =>
    cases h_rest with
    | inl h2 =>
      subst h2
      decide
    | inr h4 =>
      subst h4
      decide


theorem collatz_sandwich (n : Nat) (h : n >= 1) :
    pessimisticStability n ≤ buleyeanPredictStability n ∧
    buleyeanPredictStability n ≤ 1000 := by
  unfold pessimisticStability buleyeanPredictStability
  simp [h]
  by_cases h_cycle : n = 1 ∨ n = 2 ∨ n = 4
  · cases h_cycle with | inl h1 => simp [h1] | inr h1 => ?_
    cases h1 with | inl h2 => simp [h2] | inr h4 => simp [h4]
  · have h_not : (n == 1 || n == 2 || n == 4) = false := by
      match h1 : (n == 1 || n == 2 || n == 4) with
      | true =>
        simp [Bool.or_eq_true, Nat.beq_eq_true_iff] at h1
        exact (h_cycle h1).elim
      | false => rfl
    simp [h_not]

end MeshCollatzConjecture
