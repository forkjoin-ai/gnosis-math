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
  have h_pos : 0 < n := by omega
  simp [h_pos]
  split <;> omega


end MeshCollatzConjecture
