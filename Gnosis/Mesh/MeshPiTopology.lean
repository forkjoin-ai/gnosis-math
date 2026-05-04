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
  constructor
  · unfold pessimisticLimit unknowability
    by_cases h1 : n > 1000
    · simp [h1]
    · have h_not_zero : (n == 0) = false := by 
        match n with | 0 => contradiction | _ + 1 => rfl
      simp [h1, h_not_zero]
      match h_div : 1000 / n with
      | 0 =>
        -- h_div : 1000 / n = 0. From Nat.div_eq_zero_iff: n = 0 ∨ 1000 < n.
        -- Both disjuncts contradict our hypotheses (h : n ≥ 1, h1 : ¬ n > 1000).
        have h_contra : n = 0 ∨ 1000 < n := Nat.div_eq_zero_iff.mp h_div
        exact h_contra.elim
          (fun hn0 => absurd (hn0 ▸ h) (by decide))
          (fun hgt => absurd hgt h1)
      | m + 1 =>
        -- Match's motive substitutes 1000/n ↦ m+1, so goal is `1 ≤ m + 1`.
        exact Nat.succ_le_succ (Nat.zero_le m)
  · constructor
    · unfold buleyeanLimit; apply Nat.le_refl
    · unfold buleyeanLimit unknowability
      split
      · exact Nat.le_refl 1000
      · apply Nat.div_le_self

end MeshPiTopology
